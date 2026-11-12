import SolarTV.MIR.Program
import SolidCore.Refinement.Generic.Simp

/-!
# Solar's first lowered MIR, run symbolically

`symTree m sel n fuel env` runs the lowered MIR module `m` (SolarTV.MIR.Lowered, the module after
`lower-evm-shaped`) on a symbolic call of selector `sel` with `n` argument words, no value and
any storage, and gives the call's outcome as a `Tree`, the object the source side computes too.
`symTreeValue m sel n fuel env` runs it the same way on a call with a value other than 0.

The run mirrors SolarTV's `moduleBlock` and `segment` step by step, with `fuel` steps along each path,
from a symbolic frame: the returns of the internal calls in progress (`SReturn`, innermost first),
the position (SolarTV's `Pos`), the symbolic values, the symbolic state and the facts of the path:

* a value is a symbolic word (`SV.w`), the first call data word (`SV.cd0`), which only its
  selector, `shr(224, ·)`, may read, or the call's value when it is not 0 (`SV.paid`), which only
  `iszero`, `eq` and `ne` against 0 and a branch may read;
* the call's inputs are known words: `callvalue` is the run's `cv` (the word 0 in `symTree`,
  `SV.paid` in `symTreeValue`), `calldatasize` is `4 + 32 * n`, the word at `4 + 32 * i` is
  argument `i`;
* pure operations of the fragment (`binOfOp`: arithmetic, comparisons, `and`, `or`, `xor`,
  `shl`, `shr`, `byte`; `iszero`, `not`, `ne`) build words, folding constants
  (`mkBin`, `mkUn`); memory is a function from byte offsets to `OByte`s, written by `mstore` at
  constant offsets;
* storage is the writes of the run (`Writes`): `sload` and `sstore` take any slot word, `sload`
  reading `Writes.read` and `sstore` writing `Writes.set`;
* a log (`log0` to `log4`) with a constant offset and size appends its topic words and its data
  bytes to the logs of the state (`SState.logs`, oldest first);
* with the environment flags `env` (`EnvFlags`), `caller` is `callerWord` when they read the
  caller, and `keccak256` of 64 bytes at a constant offset whose memory holds two words
  (`memWord`) is `WExpr.hash` of them when they hash, as an oracle that `MirRun.EnvAsk`
  describes computes them; otherwise neither has a run;
* an `assume` needs its word, simplified on the facts of the path (`WExpr.simp`), to be a
  constant of the side it states;
* an internal call runs the instructions before it, pushes its return and enters the callee's
  block 0 with its parameters bound; a `leave` pops the innermost return and binds the call's
  result (`symBindResult`), as SolarTV's `bindResult` does; a tail call enters the callee and
  keeps the returns; a call that binds or publishes further results (a callee returning several
  words), a callee or an entry function that stores an entry heap (`Function.entryHeap`), and
  `heap_floor` and `alloc` are outside the fragment;
* a branch on a constant takes its side, a branch on `SV.paid` its nonzero side, a branch on any
  other word becomes a `Tree.ite` whose sides run with the word as one more fact (`Facts.add`),
  a switch needs a constant key and constant cases;
* `return` and `revert` with constant offsets and sizes read the bytes of memory; a success keeps
  the writes and the logs.

Anything else (another effect, a symbolic memory offset, phis without the predecessor, a
`leave` with no call in progress, running out of fuel) makes the run `none`, so the check that
uses it fails rather than trusting it. `MirRun.symTree_sound` and `MirRun.symTreeValue_sound`
prove that the module's run shows the tree's result.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered EvmRules

/-! ## Symbolic values and states -/

/-- A symbolic value: a word of the call, the first word of its call data, or its value when
that is not 0. -/
inductive SV where
  | w (e : WExpr)
  | cd0
  | paid
  deriving DecidableEq, Repr

abbrev SEnv := Nat → SV

def SEnv.set (env : SEnv) (id : Nat) (v : SV) : SEnv := fun j => if j = id then v else env j

def SV.ofOperand (env : SEnv) : Operand → SV
  | .value id => env id
  | .const word => .w (.lit word.toNat)

/-- A symbolic machine state: memory bytes, the storage writes (newest first) and the logs
(oldest first). -/
structure SState where
  mem : Nat → OByte
  writes : Writes
  logs : List Log

/-- The state a call starts in: zero memory, no writes, no logs. -/
def SState.initial : SState := ⟨fun _ => .lit 0, [], []⟩

def storeBytes (mem : Nat → OByte) (off : Nat) (e : WExpr) : Nat → OByte :=
  fun i => if off ≤ i ∧ i < off + 32 then .byteOf e (i - off) else mem i

/-- The word the 32 bytes of memory at `off` are, when they are the bytes of one word in order. -/
def memWord (mem : Nat → OByte) (off : Nat) : Option WExpr :=
  match mem off with
  | .byteOf e _ =>
    if (List.range 32).all (fun i => mem (off + i) == .byteOf e i) then some e else none
  | .lit _ => none

/-- The words of symbolic values that are all words. -/
def svWords : List SV → Option (List WExpr)
  | [] => some []
  | .w e :: rest => (svWords rest).map (e :: ·)
  | _ :: _ => none

def calldataArg (n off : Nat) : Option SV :=
  if off = 0 then some .cd0
  else if 4 ≤ off ∧ (off - 4) % 32 = 0 ∧ (off - 4) / 32 < n then some (.w (.arg ((off - 4) / 32)))
  else none

def binOfOp : EVM.Op → Option BinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .lt => some .lt
  | .gt => some .gt
  | .eq => some .eq
  | .and => some .and
  | .or => some .or
  | .xor => some .xor
  | .shl => some .shl
  | .shr => some .shr
  | .byte => some .byte
  | _ => none

def symPure (sel : Nat) : EVM.Op → List SV → Option SV
  | .shr, [.w (.lit 224), .cd0] => some (.w (.lit sel))
  | .iszero, [.w a] => some (.w (mkUn .iszero a))
  | .not, [.w a] => some (.w (mkUn .not a))
  | op, [.w a, .w b] => (binOfOp op).map fun o => .w (mkBin o a b)
  -- A value other than 0: `iszero` is 0, and so is `eq` against 0.
  | .iszero, [.paid] => some (.w (.lit 0))
  | .eq, [.paid, .w (.lit z)] => if z % wordSize = 0 then some (.w (.lit 0)) else none
  | .eq, [.w (.lit z), .paid] => if z % wordSize = 0 then some (.w (.lit 0)) else none
  | _, _ => none

def outBytes (mem : Nat → OByte) (off size : Nat) : List OByte :=
  (List.range size).map fun i => mem (off + i)

/-- The environment reads the symbolic run may take: `caller` (as `callerWord`) and
`keccak256` of two words (as `hash`). -/
structure EnvFlags where
  caller : Bool
  hash : Bool
  deriving DecidableEq, Repr

/-- No environment read. -/
def EnvFlags.off : EnvFlags := ⟨false, false⟩

/-- The caller and the hash of two words. -/
def EnvFlags.all : EnvFlags := ⟨true, true⟩

/-- The caller only. -/
def EnvFlags.callerOnly : EnvFlags := ⟨true, false⟩

/-- An effect on symbolic operands: its result and the state after it. `ev` says which
environment reads `caller` and `keccak256` may take. -/
def symEffect (ev : EnvFlags) (cv : SV) (n : Nat) : Effect → List SV → SState → Option (Option SV × SState)
  | .calldatasize, [], st => some (some (.w (.lit (4 + 32 * n))), st)
  | .callvalue, [], st => some (some cv, st)
  | .calldataload, [.w (.lit off)], st => (calldataArg n (off % wordSize)).map fun v => (some v, st)
  | .sload, [.w k], st => some (some (.w (st.writes.read k)), st)
  | .sstore, [.w k, .w e], st => some (none, { st with writes := st.writes.set k e })
  | .mstore, [.w (.lit off), .w e], st =>
    some (none, { st with mem := storeBytes st.mem (off % wordSize) e })
  | .caller, [], st => if ev.caller = true then some (some (.w (.lit callerWord)), st) else none
  | .keccak256, [.w (.lit off), .w (.lit size)], st =>
    if ev.hash = true ∧ size % wordSize = 64 then
      match memWord st.mem (off % wordSize), memWord st.mem (off % wordSize + 32) with
      | some a, some b => some (some (.w (.hash a b)), st)
      | _, _ => none
    else none
  | .log k, .w (.lit off) :: .w (.lit size) :: topics, st =>
    if topics.length = k then
      match svWords topics with
      | some ts =>
        some (none, { st with
          logs := st.logs ++ [⟨ts, outBytes st.mem (off % wordSize) (size % wordSize)⟩] })
      | none => none
    else none
  | _, _, _ => none

/-- The instructions of a block up to its first internal call, on the facts `K` of the path. -/
def symInsts (ev : EnvFlags) (cv : SV) (sel n : Nat) (K : Facts) :
    List Inst → SEnv → SState → Option (SEnv × SState)
  | [], env, st => some (env, st)
  | .pure dst op args :: rest, env, st =>
    match symPure sel op (args.map (SV.ofOperand env)) with
    | some v => symInsts ev cv sel n K rest (env.set dst v) st
    | none => none
  | .effect dst eff args :: rest, env, st =>
    match symEffect ev cv n eff (args.map (SV.ofOperand env)) st with
    | some (res, st') =>
      let env := match dst, res with
        | some d, some v => env.set d v
        | _, _ => env
      symInsts ev cv sel n K rest env st'
    | none => none
  | .ne dst a b :: rest, env, st =>
    match SV.ofOperand env a, SV.ofOperand env b with
    | .w x, .w y => symInsts ev cv sel n K rest (env.set dst (.w (mkUn .iszero (mkBin .eq x y)))) st
    -- A value other than 0 is not 0.
    | .paid, .w (.lit z) =>
      if z % wordSize = 0 then symInsts ev cv sel n K rest (env.set dst (.w (.lit 1))) st else none
    | .w (.lit z), .paid =>
      if z % wordSize = 0 then symInsts ev cv sel n K rest (env.set dst (.w (.lit 1))) st else none
    | _, _ => none
  | .assume negated op args :: rest, env, st =>
    match symPure sel op (args.map (SV.ofOperand env)) with
    | some (.w e) =>
      match (e.simp K).lit? with
      | some v =>
        if v % wordSize = 0 then (if negated then symInsts ev cv sel n K rest env st else none)
        else (if negated then none else symInsts ev cv sel n K rest env st)
      | none => none
    | _ => none
  -- Outside the fragment (a cast, a low-bits mask, a select, a heap floor, an allocation) or
  -- an internal call, which
  -- `symSegment` splits off first: no run.
  | _ :: _, _, _ => none

def symPhis (incoming : SEnv) (pred : Nat) :
    List (Nat × List (Nat × Operand)) → SEnv → Option SEnv
  | [], env => some env
  | (dst, arms) :: rest, env =>
    match arms.find? (fun arm => arm.1 == pred) with
    | some (_, op) => symPhis incoming pred rest (env.set dst (SV.ofOperand incoming op))
    | none => none

def symSwitch (env : SEnv) (key default : Nat) : List (Operand × Nat) → Option Nat
  | [] => some default
  | (c, t) :: rest =>
    match SV.ofOperand env c with
    | .w (.lit v) => if v % wordSize = key % wordSize then some t else symSwitch env key default rest
    | _ => none

def symBindParams : List Nat → List SV → SEnv → Option SEnv
  | [], [], env => some env
  | p :: ps, a :: as, env => symBindParams ps as (env.set p a)
  | _, _, _ => none

/-- The caller's values after a return, as SolarTV's `bindResult`. -/
def symBindResult (env : SEnv) : Option Nat → List SV → Option SEnv
  | none, [] => some env
  | some dst, [v] => some (env.set dst v)
  | _, _ => none

/-! ## Frames and steps -/

/-- Where an internal call returns, as SolarTV's `Return`, with symbolic values. -/
structure SReturn where
  fn : Nat
  block : Nat
  dst : Option Nat
  rest : List Inst
  term : Terminator
  env : SEnv

/-- The callee of an internal or tail call, when the module has it and it stores no entry heap
on entering it (`Function.entryHeap`, outside the fragment): then entering it keeps the state
(`Function.start`). -/
def symCallee (m : Module) (callee : Nat) : Option Function :=
  match m.functions[callee]? with
  | some g => if g.entryHeap.isNone then some g else none
  | none => none

/-- Whether the module's entry function stores no entry heap when the run starts
(`Module.startState`), so that the run starts in the call's initial state. -/
def entryFree (m : Module) : Bool :=
  match m.functions[m.entry]? with
  | some f => f.entryHeap.isNone
  | none => true

/-- What one step of the symbolic run gives: an end, the next frame, or a branch on a word to
block `yes` or `no` of function `fn` from block `b`. -/
inductive SNext where
  | done (T : Tree)
  | go (stack : List SReturn) (pos : Pos) (env : SEnv) (st : SState)
  | fork (e : WExpr) (stack : List SReturn) (fn b yes no : Nat) (env : SEnv) (st : SState)

/-- A block's terminator after its instructions. -/
def symTerm (m : Module) (stack : List SReturn) (fn b : Nat) (env : SEnv) (st : SState) :
    Terminator → Option SNext
  | .jump t => some (.go stack (.enter fn b t) env st)
  | .branch c yes no =>
    match SV.ofOperand env c with
    | .w e =>
      match e.lit? with
      | some v => some (.go stack (.enter fn b (if v % wordSize = 0 then no else yes)) env st)
      | none => some (.fork e stack fn b yes no env st)
    | .cd0 => none
    | .paid => some (.go stack (.enter fn b yes) env st)
  | .switch k d cs =>
    match SV.ofOperand env k with
    | .w (.lit kv) =>
      match symSwitch env kv d cs with
      | some t => some (.go stack (.enter fn b t) env st)
      | none => none
    | _ => none
  | .tailCall callee args =>
    match symCallee m callee with
    | none => none
    | some g =>
      match symBindParams g.params (args.map (SV.ofOperand env)) (fun _ => .w (.lit 0)) with
      | none => none
      | some env' => some (.go stack (.enter callee 0 0) env' st)
  | .leave values =>
    match stack with
    | [] => none
    | ret :: stack =>
      match symBindResult ret.env ret.dst (values.map (SV.ofOperand env)) with
      | none => none
      | some env' => some (.go stack (.resume ret.fn ret.block ret.rest ret.term) env' st)
  | .ret off size =>
    match SV.ofOperand env off, SV.ofOperand env size with
    | .w (.lit o), .w (.lit s) =>
      some (.done (.halt true (outBytes st.mem (o % wordSize) (s % wordSize)) st.writes st.logs))
    | _, _ => none
  | .revert off size =>
    match SV.ofOperand env off, SV.ofOperand env size with
    | .w (.lit o), .w (.lit s) =>
      some (.done (.halt false (outBytes st.mem (o % wordSize) (s % wordSize)) [] []))
    | _, _ => none
  | .stop => some (.done (.halt true [] st.writes st.logs))
  | .invalid => some (.done (.halt false [] [] []))

/-- The rest of a block from its instructions, as SolarTV's `segment`. -/
def symSegment (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (K : Facts) (stack : List SReturn)
    (fn b : Nat) (insts : List Inst) (term : Terminator) (env : SEnv) (st : SState) :
    Option SNext :=
  match splitCall insts with
  | (before, some (dst, callee, args, [], none, rest)) =>
    match symInsts ev cv sel n K before env st with
    | none => none
    | some (env, st) =>
      match symCallee m callee with
      | none => none
      | some g =>
        match symBindParams g.params (args.map (SV.ofOperand env)) (fun _ => .w (.lit 0)) with
        | none => none
        | some inner => some (.go (⟨fn, b, dst, rest, term, env⟩ :: stack) (.enter callee 0 0) inner st)
  -- A call that binds or publishes further results (a callee returning several words):
  -- outside the fragment.
  | (_, some _) => none
  | (before, none) =>
    match symInsts ev cv sel n K before env st with
    | none => none
    | some (env, st) => symTerm m stack fn b env st term

/-- One step of the module, as SolarTV's `moduleBlock`. -/
def symStep (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (K : Facts) :
    List SReturn → Pos → SEnv → SState → Option SNext
  | stack, .enter fn pred b, env, st =>
    match m.functions[fn]? with
    | none => none
    | some f =>
      match f.blocks[b]? with
      | none => none
      | some blk =>
        match symPhis env pred blk.phis env with
        | none => none
        | some env => symSegment ev cv m sel n K stack fn b blk.insts blk.term env st
  | stack, .resume fn b insts term, env, st => symSegment ev cv m sel n K stack fn b insts term env st

/-- The symbolic run, one step per unit of fuel; a branch on a word runs both sides, each with
the word's side as one more fact. -/
def symRun (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) :
    Nat → List SReturn → Pos → SEnv → SState → Facts → Option Tree
  | 0, _, _, _, _, _ => none
  | fuel + 1, stack, pos, env, st, K =>
    match symStep ev cv m sel n K stack pos env st with
    | none => none
    | some (.done T) => some T
    | some (.go stack pos env st) => symRun ev cv m sel n fuel stack pos env st K
    | some (.fork e stack fn b yes no env st) =>
      match symRun ev cv m sel n fuel stack (.enter fn b yes) env st (K.add e true),
        symRun ev cv m sel n fuel stack (.enter fn b no) env st (K.add e false) with
      | some t, some f => some (.ite e t f)
      | _, _ => none

/-- The tree of a call of selector `sel` on `n` argument words, from the module's entry. -/
def symTree (m : Module) (sel n fuel : Nat) (env : EnvFlags := .off) : Option Tree :=
  if entryFree m then
    symRun env (.w (.lit 0)) m sel n fuel [] (.enter m.entry 0 0) (fun _ => .w (.lit 0)) SState.initial []
  else none

/-- The tree of a call of selector `sel` on `n` argument words with a value other than 0, from
the module's entry. -/
def symTreeValue (m : Module) (sel n fuel : Nat) (env : EnvFlags := .off) : Option Tree :=
  if entryFree m then
    symRun env .paid m sel n fuel [] (.enter m.entry 0 0) (fun _ => .w (.lit 0)) SState.initial []
  else none

end SolidCore.Refinement.Generic
