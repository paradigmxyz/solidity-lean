import SolidCore.Refinement.Generic.CallTree
import SolidCore.Refinement.Generic.Mir

/-!
# Solar's first lowered MIR with one external call, run symbolically

`symTreeC m sel n fuel env` runs the lowered MIR module `m` on a symbolic call of selector `sel`
with `n` argument words, as `symTree` does (Generic/Mir.lean), and gives the call's outcome as a
call tree (`CTree`, Generic/CallTree.lean): the run may make one external call on each path, a
`STATICCALL` whose target is a word, whose value is zero and whose input and output ranges are
constants.

* Before the call (the pre-phase) the run is `symTree`'s, with one more effect: `gas`, whose word
  (`CV.gas`) only a call's gas operand may read, since no request records the gas forwarded.
* At the call the run records the request (target, input bytes from memory) and the writes so
  far, and goes on twice from the instruction after it (the post-phase): once with the success
  flag 1, which must end in a plain tree, and once with the flag 0, which must end by bubbling
  the return data (`returndatacopy(d, 0, returndatasize())`, then `revert(d, returndatasize())`).
* After the call the size of the return data is the word `arg n` and its words `arg (n + 1 + k)`
  (the answer's words of `Val.withAns`). The call writes the first `min outSize size` bytes of the
  return data at its output offset: the run branches on `lt (arg n) (lit outSize)` (the check
  Solidity's decoder makes): with at least `outSize` bytes the output range holds the bytes of the
  answer's words, otherwise each byte `j` of it is the answer's byte when `j` is below the size and
  the byte before the call otherwise (a select).
* A branch on a word the path's facts decide takes that side (so the decoder's own check of the
  size takes the side the run's branch at the call took).

Every other effect after the call is `symTree`'s (`symEffect`); a second external call, a gas
read after the call, a call that is not a `STATICCALL`, or anything else outside the fragment
makes the run `none`. `CallMirRun.symTreeC_sound` proves the run sound.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered EvmRules

/-! ## Values -/

/-- A symbolic value of the call fragment: one of the call-free run, or a gas word, which any word
holds and only a call's gas operand reads. -/
inductive CV where
  | v (x : SV)
  | gas
  deriving DecidableEq, Repr

abbrev CEnv := Nat → CV

def CEnv.set (env : CEnv) (id : Nat) (x : CV) : CEnv := fun j => if j = id then x else env j

def CV.ofOperand (env : CEnv) : Operand → CV
  | .value id => env id
  | .const word => .v (.w (.lit word.toNat))

/-- The value of the call-free run, if it is one. -/
def CV.sv : CV → Option SV
  | .v x => some x
  | .gas => none

def cvSVs : List CV → Option (List SV)
  | [] => some []
  | x :: xs =>
    match x.sv, cvSVs xs with
    | some a, some r => some (a :: r)
    | _, _ => none

/-! ## The memory a call writes -/

/-- A byte of memory as a word below `256`. -/
def OByte.word : OByte → WExpr
  | .lit b => .lit (b % 256)
  | .byteOf e i => if i < 32 then .bin .byte (.lit i) e else .bin .and e (.lit 255)

/-- Byte `j` of the return data, read from the answer's words after the `n` argument words. -/
def retByte (n j : Nat) : WExpr := .bin .byte (.lit (j % 32)) (.arg (n + 1 + j / 32))

/-- The memory after a call whose output range is `off, size`, when the return data has at least
`size` bytes: the answer's bytes there. -/
def memLong (mem : Nat → OByte) (n off size : Nat) : Nat → OByte := fun i =>
  if off ≤ i ∧ i < off + size then .byteOf (.arg (n + 1 + (i - off) / 32)) ((i - off) % 32) else mem i

/-- The memory after a call whose output range is `off, size`, when the return data has fewer than
`size` bytes: the answer's byte below its size, the old byte past it. -/
def memShort (mem : Nat → OByte) (n off size : Nat) : Nat → OByte := fun i =>
  if off ≤ i ∧ i < off + size then
    .byteOf (.sel (.bin .lt (.arg n) (.lit (i - off + 1))) (mem i).word (retByte n (i - off))) 31
  else mem i

/-- The check of the size of the return data against the output range: `size < outSize`. -/
def shortCond (n size : Nat) : WExpr := .bin .lt (.arg n) (.lit size)

/-! ## Effects -/

/-- An effect before the external call: a gas read, or one of the call-free run's. -/
def symEffectPre (ev : EnvFlags) (cv : SV) (n : Nat) (eff : Effect) (args : List CV) (st : SState) :
    Option (Option CV × SState) :=
  match eff, args with
  | .gas, [] => some (some .gas, st)
  | .gas, _ => none
  | .call _, _ => none
  | .returndatasize, _ => none
  | .returndatacopy, _ => none
  | eff, args =>
    match cvSVs args with
    | some sargs =>
      match symEffect ev cv n eff sargs st with
      | some (r, st') => some (r.map CV.v, st')
      | none => none
    | none => none

/-- An effect after the external call, with `rdc` the offset the whole return data was copied to,
if it was: the size of the return data, the copy of all of it, or one of the call-free run's
(none of them once the return data was copied). -/
def symEffectPost (ev : EnvFlags) (cv : SV) (n : Nat) (eff : Effect) (args : List CV) (st : SState)
    (rdc : Option Nat) : Option (Option CV × SState × Option Nat) :=
  match eff, args with
  | .returndatasize, [] => some (some (.v (.w (.arg n))), st, rdc)
  | .returndatasize, _ => none
  | .returndatacopy, [.v (.w (.lit d)), .v (.w (.lit 0)), .v (.w (.arg i))] =>
    if i = n ∧ rdc = none then some (none, st, some (d % wordSize)) else none
  | .returndatacopy, _ => none
  | .gas, _ => none
  | .call _, _ => none
  | eff, args =>
    match rdc with
    | some _ => none
    | none =>
      match cvSVs args with
      | some sargs =>
        match symEffect ev cv n eff sargs st with
        | some (r, st') => some (r.map CV.v, st', none)
        | none => none
      | none => none

/-- Where the run is with respect to the external call: before it, or after it (with the
offset the return data was copied to, if it was). -/
inductive Phase where
  | pre
  | post (rdc : Option Nat)
  deriving DecidableEq, Repr

def symEffectC (ev : EnvFlags) (cv : SV) (n : Nat) (eff : Effect) (args : List CV) (st : SState) :
    Phase → Option (Option CV × SState × Phase)
  | .pre =>
    match symEffectPre ev cv n eff args st with
    | some (r, st') => some (r, st', .pre)
    | none => none
  | .post rdc =>
    match symEffectPost ev cv n eff args st rdc with
    | some (r, st', rdc') => some (r, st', .post rdc')
    | none => none

/-- The instructions of a block up to its first internal call, on the facts `K` of the path. -/
def symInstsC (ev : EnvFlags) (cv : SV) (sel n : Nat) (K : Facts) :
    List Inst → CEnv → SState → Phase → Option (CEnv × SState × Phase)
  | [], env, st, ph => some (env, st, ph)
  | .pure dst op args :: rest, env, st, ph =>
    match cvSVs (args.map (CV.ofOperand env)) with
    | some sargs =>
      match symPure sel op sargs with
      | some v => symInstsC ev cv sel n K rest (env.set dst (.v v)) st ph
      | none => none
    | none => none
  | .effect dst eff args :: rest, env, st, ph =>
    match symEffectC ev cv n eff (args.map (CV.ofOperand env)) st ph with
    | some (res, st', ph') =>
      let env := match dst, res with
        | some d, some v => env.set d v
        | _, _ => env
      symInstsC ev cv sel n K rest env st' ph'
    | none => none
  | .ne dst a b :: rest, env, st, ph =>
    match CV.ofOperand env a, CV.ofOperand env b with
    | .v (.w x), .v (.w y) =>
      symInstsC ev cv sel n K rest (env.set dst (.v (.w (mkUn .iszero (mkBin .eq x y))))) st ph
    | .v .paid, .v (.w (.lit z)) =>
      if z % wordSize = 0 then symInstsC ev cv sel n K rest (env.set dst (.v (.w (.lit 1)))) st ph
      else none
    | .v (.w (.lit z)), .v .paid =>
      if z % wordSize = 0 then symInstsC ev cv sel n K rest (env.set dst (.v (.w (.lit 1)))) st ph
      else none
    | _, _ => none
  | .assume negated op args :: rest, env, st, ph =>
    match cvSVs (args.map (CV.ofOperand env)) with
    | some sargs =>
      match symPure sel op sargs with
      | some (.w e) =>
        match (e.simp K).decided K with
        | some v =>
          if v % wordSize = 0 then (if negated then symInstsC ev cv sel n K rest env st ph else none)
          else (if negated then none else symInstsC ev cv sel n K rest env st ph)
        | none => none
      | _ => none
    | none => none
  | .word dst a :: rest, env, st, ph =>
    match CV.ofOperand env a with
    | .v (.w e) => symInstsC ev cv sel n K rest (env.set dst (.v (.w e))) st ph
    | _ => none
  | .heapFloor dst floor :: rest, env, st, ph =>
    symInstsC ev cv sel n K rest (env.set dst (.v (.w (.lit floor.toNat)))) st ph
  | _ :: _, _, _, _ => none

/-! ## Frames -/

/-- Where an internal call returns, with values of the call fragment. -/
structure CReturn where
  fn : Nat
  block : Nat
  dst : Option Nat
  rest : List Inst
  term : Terminator
  env : CEnv

def symPhisC (incoming : CEnv) (pred : Nat) :
    List (Nat × List (Nat × Operand)) → CEnv → Option CEnv
  | [], env => some env
  | (dst, arms) :: rest, env =>
    match arms.find? (fun arm => arm.1 == pred) with
    | some (_, op) => symPhisC incoming pred rest (env.set dst (CV.ofOperand incoming op))
    | none => none

def symSwitchC (env : CEnv) (key default : Nat) : List (Operand × Nat) → Option Nat
  | [] => some default
  | (c, t) :: rest =>
    match CV.ofOperand env c with
    | .v (.w (.lit v)) => if v % wordSize = key % wordSize then some t else symSwitchC env key default rest
    | _ => none

def symBindParamsC : List Nat → List CV → CEnv → Option CEnv
  | [], [], env => some env
  | p :: ps, a :: as, env => symBindParamsC ps as (env.set p a)
  | _, _, _ => none

def symBindResultC (env : CEnv) : Option Nat → List CV → Option CEnv
  | none, [] => some env
  | some dst, [v] => some (env.set dst v)
  | _, _ => none

/-- An external call instruction: a `STATICCALL` effect, with its destination and operands. -/
def isExtCall : Inst → Option (Option Nat × List Operand)
  | .effect dst (.call .staticcall) args => some (dst, args)
  | _ => none

/-- An internal call instruction. -/
def instIsCall : Inst → Bool
  | .call .. => true
  | _ => false

/-- The instructions before the first external call of a block's instructions, that call's
destination and operands, and the instructions after it; none when an internal call or no
external call comes first. -/
def splitExt : List Inst → Option (List Inst × Option Nat × List Operand × List Inst)
  | [] => none
  | inst :: rest =>
    match isExtCall inst with
    | some (dst, args) => some ([], dst, args, rest)
    | none =>
      if instIsCall inst then none
      else
        match splitExt rest with
        | some (pre, dst, args, post) => some (inst :: pre, dst, args, post)
        | none => none

/-- What one step of the run gives: an end, a bubbled failure, the next frame, a branch on a
word, or the external call with its request, the writes before it, where the run goes on after
it (the call's destination and the position after the call) and the output range. -/
inductive CNext where
  | done (T : Tree)
  | bubble
  | go (stack : List CReturn) (pos : Pos) (env : CEnv) (st : SState) (ph : Phase)
  | fork (e : WExpr) (stack : List CReturn) (fn b yes no : Nat) (env : CEnv) (st : SState) (ph : Phase)
  | callAt (r : CReq) (stack : List CReturn) (dst : Option Nat) (pos : Pos) (env : CEnv) (st : SState)
      (outOff outSize : Nat)

/-- A memory range a terminator may read: anything before the return data was copied. -/
def readOk : Phase → Bool
  | .pre => true
  | .post none => true
  | .post (some _) => false

def symTermC (m : Module) (n : Nat) (K : Facts) (stack : List CReturn) (fn b : Nat) (env : CEnv)
    (st : SState) (ph : Phase) : Terminator → Option CNext
  | .jump t => some (.go stack (.enter fn b t) env st ph)
  | .branch c yes no =>
    match CV.ofOperand env c with
    | .v (.w e) =>
      match e.lit? with
      | some v => some (.go stack (.enter fn b (if v % wordSize = 0 then no else yes)) env st ph)
      | none =>
        match K.lookup e with
        | some s => some (.go stack (.enter fn b (if s then yes else no)) env st ph)
        | none => some (.fork e stack fn b yes no env st ph)
    | .v .paid => some (.go stack (.enter fn b yes) env st ph)
    | _ => none
  | .switch k d cs =>
    match CV.ofOperand env k with
    | .v (.w (.lit kv)) =>
      match symSwitchC env kv d cs with
      | some t => some (.go stack (.enter fn b t) env st ph)
      | none => none
    | _ => none
  | .tailCall callee args =>
    match symCallee m callee with
    | none => none
    | some g =>
      match symBindParamsC g.params (args.map (CV.ofOperand env)) (fun _ => .v (.w (.lit 0))) with
      | none => none
      | some env' => if readOk ph then some (.go stack (.enter callee 0 0) env' (symStart g st) ph) else none
  | .leave values =>
    match stack with
    | [] => none
    | ret :: stack =>
      match symBindResultC ret.env ret.dst (values.map (CV.ofOperand env)) with
      | none => none
      | some env' => some (.go stack (.resume ret.fn ret.block ret.rest ret.term) env' st ph)
  | .ret off size =>
    match CV.ofOperand env off, CV.ofOperand env size with
    | .v (.w (.lit o)), .v (.w (.lit s)) =>
      if readOk ph then
        some (.done (.halt true (outBytes st.mem (o % wordSize) (s % wordSize)) st.writes st.logs))
      else none
    | _, _ => none
  | .revert off size =>
    match ph, CV.ofOperand env off, CV.ofOperand env size with
    | .post (some d), .v (.w (.lit o)), .v (.w (.arg i)) =>
      if o % wordSize = d ∧ i = n then some .bubble else none
    | ph, .v (.w (.lit o)), .v (.w (.lit s)) =>
      if readOk ph then
        some (.done (.halt false (outBytes st.mem (o % wordSize) (s % wordSize)) [] []))
      else none
    | _, _, _ => none
  | .stop => if readOk ph then some (.done (.halt true [] st.writes st.logs)) else none
  | .invalid => some (.done (.halt false [] [] []))

/-- The rest of a block from its instructions with no external call, as SolarTV's `segment`. -/
def symSegmentPlain (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (K : Facts)
    (stack : List CReturn) (fn b : Nat) (insts : List Inst) (term : Terminator) (env : CEnv)
    (st : SState) (ph : Phase) : Option CNext :=
  match splitCall insts with
  | (before, some (dst, callee, args, [], none, rest)) =>
    match symInstsC ev cv sel n K before env st ph with
    | none => none
    | some (env, st, ph) =>
      match symCallee m callee with
      | none => none
      | some g =>
        match symBindParamsC g.params (args.map (CV.ofOperand env)) (fun _ => .v (.w (.lit 0))) with
        | none => none
        | some inner =>
          if readOk ph then
            some (.go (⟨fn, b, dst, rest, term, env⟩ :: stack) (.enter callee 0 0) inner (symStart g st) ph)
          else none
  | (_, some _) => none
  | (before, none) =>
    match symInstsC ev cv sel n K before env st ph with
    | none => none
    | some (env, st, ph) => symTermC m n K stack fn b env st ph term

/-- The rest of a block from its instructions: before the external call, the call when the
instructions reach it first; otherwise as SolarTV's `segment`. -/
def symSegmentC (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (K : Facts)
    (stack : List CReturn) (fn b : Nat) (insts : List Inst) (term : Terminator) (env : CEnv)
    (st : SState) (ph : Phase) : Option CNext :=
  match ph, splitExt insts with
  | .pre, some (pre, dst, args, post) =>
    match symInstsC ev cv sel n K pre env st .pre with
    | some (env', st', .pre) =>
      match args.map (CV.ofOperand env') with
      | [_, .v (.w e), .v (.w (.lit io)), .v (.w (.lit is)), .v (.w (.lit oo)), .v (.w (.lit os))] =>
        some (.callAt ⟨true, e, .lit 0, outBytes st'.mem (io % wordSize) (is % wordSize)⟩ stack dst
          (.resume fn b post term) env' st' (oo % wordSize) (os % wordSize))
      | _ => none
    | _ => none
  | _, _ => symSegmentPlain ev cv m sel n K stack fn b insts term env st ph

/-- One step of the module, as SolarTV's `moduleBlock`. -/
def symStepC (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (K : Facts) :
    List CReturn → Pos → CEnv → SState → Phase → Option CNext
  | stack, .enter fn pred b, env, st, ph =>
    match m.functions[fn]? with
    | none => none
    | some f =>
      match f.blocks[b]? with
      | none => none
      | some blk =>
        match symPhisC env pred blk.phis env with
        | none => none
        | some env => symSegmentC ev cv m sel n K stack fn b blk.insts blk.term env st ph
  | stack, .resume fn b insts term, env, st, ph => symSegmentC ev cv m sel n K stack fn b insts term env st ph

/-- How the run after the call ends on every path: a plain tree, or a bubbled failure on
every path. -/
inductive POut where
  | tree (T : Tree)
  | bubble
  deriving DecidableEq, Repr

/-- The run after the external call, one step per unit of fuel. -/
def symRunPost (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) :
    Nat → List CReturn → Pos → CEnv → SState → Phase → Facts → Option POut
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, stack, pos, env, st, ph, K =>
    match ph with
    | .pre => none
    | .post _ =>
      match symStepC ev cv m sel n K stack pos env st ph with
      | some (.done T) => some (.tree T)
      | some .bubble => some .bubble
      | some (.go stack pos env st ph) => symRunPost ev cv m sel n fuel stack pos env st ph K
      | some (.fork e stack fn b yes no env st ph) =>
        match symRunPost ev cv m sel n fuel stack (.enter fn b yes) env st ph (K.add e true),
          symRunPost ev cv m sel n fuel stack (.enter fn b no) env st ph (K.add e false) with
        | some (.tree t), some (.tree f) => some (.tree (.ite e t f))
        | some .bubble, some .bubble => some .bubble
        | _, _ => none
      | _ => none

/-- The value a call's destination holds after it: the success flag. -/
def setDst (env : CEnv) : Option Nat → Nat → CEnv
  | none, _ => env
  | some d, flag => env.set d (.v (.w (.lit flag)))

/-- The run after the external call with the flag `flag`, from the memory the call leaves: with
no output range the memory before it; otherwise a branch on the size of the return data against
the output range, each side with its memory. -/
def symRunAfter (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) (fuel : Nat)
    (stack : List CReturn) (dst : Option Nat) (pos : Pos) (env : CEnv) (st : SState)
    (oo os : Nat) (K : Facts) (flag : Nat) : Option POut :=
  let env := setDst env dst flag
  if os = 0 then symRunPost ev cv m sel n fuel stack pos env st (.post none) K
  else
    match symRunPost ev cv m sel n fuel stack pos env { st with mem := memShort st.mem n oo os }
        (.post none) (K.add (shortCond n os) true),
      symRunPost ev cv m sel n fuel stack pos env { st with mem := memLong st.mem n oo os }
        (.post none) (K.add (shortCond n os) false) with
    | some (.tree t), some (.tree f) => some (.tree (.ite (shortCond n os) t f))
    | some .bubble, some .bubble => some .bubble
    | _, _ => none

/-- The run before the external call, one step per unit of fuel: a plain tree on a path that
makes no call, and the call node where it makes one, whose success goes on as a plain tree and
whose failure bubbles. -/
def symRunPre (ev : EnvFlags) (cv : SV) (m : Module) (sel n : Nat) :
    Nat → List CReturn → Pos → CEnv → SState → Facts → Option CTree
  | 0, _, _, _, _, _ => none
  | fuel + 1, stack, pos, env, st, K =>
    match symStepC ev cv m sel n K stack pos env st .pre with
    | some (.done T) => some (.tree T)
    | some (.go stack pos env st .pre) => symRunPre ev cv m sel n fuel stack pos env st K
    | some (.fork e stack fn b yes no env st .pre) =>
      match symRunPre ev cv m sel n fuel stack (.enter fn b yes) env st (K.add e true),
        symRunPre ev cv m sel n fuel stack (.enter fn b no) env st (K.add e false) with
      | some t, some f => some (.ite e t f)
      | _, _ => none
    | some (.callAt r stack dst pos env st oo os) =>
      match symRunAfter ev cv m sel n fuel stack dst pos env st oo os K 1,
        symRunAfter ev cv m sel n fuel stack dst pos env st oo os K 0 with
      | some (.tree t), some .bubble => some (.call r st.writes n t)
      | _, _ => none
    | _ => none

/-- The call tree of a call of selector `sel` on `n` argument words, from the module's entry. -/
def symTreeC (m : Module) (sel n fuel : Nat) (env : EnvFlags := .off) : Option CTree :=
  symRunPre env (.w (.lit 0)) m sel n fuel [] (.enter m.entry 0 0) (fun _ => .v (.w (.lit 0)))
    (symEntryStart m SState.initial) []

end SolidCore.Refinement.Generic

