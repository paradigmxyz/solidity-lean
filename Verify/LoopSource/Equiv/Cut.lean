import SolidCore.Refinement.Generic.MirRun
import Verify.LoopSource.Generic.Interface

/-!
# Cut points of a loop in solar's lowered MIR: the certificate and its check

A loop-carrying function's lowered MIR has a block its loop comes back to, the **header**. The
symbolic run of the module (`symStep`, `Mir.lean`) cannot run it to an end: it would unroll the
loop. `cutRun` runs it the same way, step by step, but stops when it enters the header, and
leaves a `back` leaf with the symbolic frame there.

A **cut-point certificate** (`Cut`) names the function, its header block, and a **template** of
the frame after the header's phis: for each value number, each memory word and each storage write
the header may hold, a `Slot`: either a **header word** `hw k` (a word the loop changes, or one the
certificate does not describe; `.arg (n + k)` of a header valuation) or a **fixed** word over
the call (`fixed e`, no argument word past the call's `n`). Everything else is zero.

`Cut.check` runs:

* the **entry run**: from the module's entry, to every end or first arrival at the header;
* the **iteration run**: from the template after the phis, to every end or arrival at the header;

once under each of the certificate's cases (facts at the header, one of which the invariant gives, as `Obl.facts` proves), and matches every arrival against the template (`matchLeaf`): it reads off the header words the
frame holds, as words over the run's valuation, and fails unless every fixed slot holds its word
and nothing outside the template was written (the footprint `Frame`, tracked along the run). It
returns the leaves of both runs as first-order data (`Out`): an end's tree, or the next header
words. A function with an internal call that returns, or an `mstore` at an offset that is not
a constant, has no check (`segFoot`).

The check is a function the kernel evaluates. What it cannot decide (the loop's invariant and
measure) is `Obl`: facts about the leaves over a header valuation, where the back-edge case is
the source loop's `LoopRecord.Step`.
-/

namespace Verify.LoopSource.Equiv
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement.Generic
open Verify.LoopSource.Interface

/-! ## Footprints -/

/-- The value numbers an instruction may bind. -/
def instDsts : Inst → List Nat
  | .pure d _ _ => [d]
  | .effect (some d) _ _ => [d]
  | .effect none _ _ => []
  | .ne d _ _ => [d]
  | .assume _ _ _ => []
  | .word d _ => [d]
  | .call d _ _ _ _ => d.toList
  | .low d _ _ => [d]
  | .select d _ _ _ => [d]
  | .heapFloor d _ => [d]
  | .alloc d _ => [d]

/-- The memory words an instruction may write: an `mstore` at a constant offset writes the word
there; `none` for an `mstore` at any other offset. -/
def instMem : Inst → Option (List Nat)
  | .effect _ .mstore (.const w :: _) => some [w.toNat % wordSize]
  | .effect _ .mstore _ => none
  | _ => some []

/-- An internal call. -/
def isCallInst : Inst → Bool
  | .call .. => true
  | _ => false

/-- What a tail call's callee binds and writes on entry: its parameters, and its entry heap's word. -/
def termFoot (m : Module) : Terminator → List Nat × List Nat
  | .tailCall callee _ =>
    match m.functions[callee]? with
    | some g => (g.params, match g.entryHeap with | some _ => [64] | none => [])
    | none => ([], [])
  | _ => ([], [])

/-- What a block's rest may bind and write: its instructions' footprints, a tail call's parameters
and its callee's entry heap; `none` when it makes an internal call or an `mstore` at an offset
that is not a constant. -/
def segFoot (m : Module) (insts : List Inst) (term : Terminator) (pre : List Nat) :
    Option (List Nat × List Nat) :=
  if insts.all (fun i => !isCallInst i) = true then
    match insts.mapM instMem with
    | none => none
    | some offs => some (pre ++ insts.flatMap instDsts ++ (termFoot m term).1, offs.flatten ++ (termFoot m term).2)
  else none

/-- The footprint of one step of the module from a position. -/
def stepFoot (m : Module) : Pos → Option (List Nat × List Nat)
  | .enter fn _ b =>
    match m.functions[fn]? with
    | none => none
    | some f =>
      match f.blocks[b]? with
      | none => none
      | some blk => segFoot m blk.insts blk.term (blk.phis.map Prod.fst)
  | .resume _ _ insts term => segFoot m insts term []

/-- Byte `i` is in a word that starts at an offset of `MO`. -/
def Covered (MO : List Nat) (i : Nat) : Prop := ∃ o ∈ MO, o ≤ i ∧ i < o + 32

/-- **The footprint holds**: values outside `D` are the word 0 and bytes outside `MO`'s words are
zero. -/
def Frame (D MO : List Nat) (senv : SEnv) (st : SState) : Prop :=
  (∀ j, j ∉ D → senv j = .w (.lit 0)) ∧ (∀ i, ¬ Covered MO i → st.mem i = .lit 0)

/-! ## The cut-point run -/

/-- The outcome of a cut-point run: an end, an arrival at the header from `pred` with the frame
there and its footprint, or a branch on a word. -/
inductive CTree where
  | done (T : Tree)
  | back (pred : Nat) (env : SEnv) (st : SState) (D MO : List Nat)
  | ite (e : WExpr) (t f : CTree)

/-- The predecessor, when the position enters the header `head` of function `fn`. -/
def atHead (fn head : Nat) : Pos → Option Nat
  | .enter fn' pred b => if fn' = fn ∧ b = head then some pred else none
  | .resume _ _ _ _ => none

/-- **The cut-point run**: `symStep` step by step with no call in progress, the footprint
tracked, until an end or an arrival at the header. -/
def cutRun (ev : EnvFlags) (cv : SV) (m : Module) (sel n fn head : Nat) :
    Nat → Pos → SEnv → SState → Facts → List Nat → List Nat → Option CTree
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, pos, senv, st, K, D, MO =>
    match atHead fn head pos with
    | some pred => some (.back pred senv st D MO)
    | none =>
      match stepFoot m pos with
      | none => none
      | some (d, mo) =>
        match symStep ev cv m sel n K [] pos senv st with
        | some (.done T) => some (.done T)
        | some (.go [] pos' senv' st') => cutRun ev cv m sel n fn head fuel pos' senv' st' K (D ++ d) (MO ++ mo)
        | some (.fork e [] fn' b yes no senv' st') =>
          match K.lookup e with
          | some false => cutRun ev cv m sel n fn head fuel (.enter fn' b no) senv' st' K (D ++ d) (MO ++ mo)
          | some true => cutRun ev cv m sel n fn head fuel (.enter fn' b yes) senv' st' K (D ++ d) (MO ++ mo)
          | none =>
            match cutRun ev cv m sel n fn head fuel (.enter fn' b yes) senv' st' (K.add e true) (D ++ d) (MO ++ mo),
              cutRun ev cv m sel n fn head fuel (.enter fn' b no) senv' st' (K.add e false) (D ++ d) (MO ++ mo) with
            | some t, some f => some (.ite e t f)
            | _, _ => none
        | _ => none

/-! ## The certificate -/

/-- A word of the header template: a header word, or a fixed word over the call. -/
inductive Slot where
  | hw (k : Nat)
  | fixed (e : WExpr)
  deriving DecidableEq, Repr

/-- **A cut-point certificate**: the loop's function and header block, the template after the
header's phis (values, memory words at their offsets, storage writes newest first), the number of
header words and the fuel of each run. -/
structure Cut where
  fn : Nat
  head : Nat
  ids : List (Nat × Slot)
  mem : List (Nat × Slot)
  writes : List (WExpr × Slot)
  nhw : Nat
  cases : List Facts
  fuel : Nat
  deriving Repr

/-- No argument word at or past `n`. -/
def argsBelow (n : Nat) : WExpr → Bool
  | .lit _ => true
  | .arg i => decide (i < n)
  | .init _ => true
  | .un _ a => argsBelow n a
  | .bin _ a b => argsBelow n a && argsBelow n b
  | .sinit k => argsBelow n k
  | .sel c a b => argsBelow n c && argsBelow n a && argsBelow n b
  | .hash a b => argsBelow n a && argsBelow n b
  | .caller => true

/-- A slot's word: header word `k` is argument `n + k` of a header valuation. -/
def Slot.expr (n : Nat) : Slot → WExpr
  | .hw k => .arg (n + k)
  | .fixed e => e

/-- The template's values: the slots', every other value the word 0. -/
def Cut.env (C : Cut) (n : Nat) : SEnv := fun j =>
  match C.ids.lookup j with
  | some s => .w (s.expr n)
  | none => .w (.lit 0)

/-- The template's word covering byte `i`, the first in the list. -/
def coverFind (i : Nat) : List (Nat × Slot) → Option (Nat × Slot)
  | [] => none
  | (o, s) :: rest => if o ≤ i ∧ i < o + 32 then some (o, s) else coverFind i rest

/-- The template's memory: byte `i` of the word covering it, every other byte zero. -/
def memOf (n : Nat) (mem : List (Nat × Slot)) (i : Nat) : OByte :=
  match coverFind i mem with
  | some (o, s) => .byteOf (s.expr n) (i - o)
  | none => .lit 0

/-- The template's state: its memory, its writes and no logs. -/
def Cut.st (C : Cut) (n : Nat) : SState :=
  ⟨memOf n C.mem, C.writes.map (fun p => (p.1, p.2.expr n)), []⟩

/-- A slot holds the word `e` of an arrival whose header words are `hs`: a header word is the one
read, a fixed word is `e` itself and over the call only. -/
def slotOk (n : Nat) (hs : List WExpr) (s : Slot) (e : WExpr) : Bool :=
  match s with
  | .hw k => decide (hs[k]? = some e)
  | .fixed f => decide (f = e) && argsBelow n f

/-- The words an arrival's values hold in the template's value slots. -/
def idPairs (senv : SEnv) : List (Nat × Slot) → Option (List (Slot × WExpr))
  | [] => some []
  | (j, s) :: rest =>
    match senv j, idPairs senv rest with
    | .w e, some ps => some ((s, e) :: ps)
    | _, _ => none

/-- The words an arrival's memory holds in the template's memory slots. -/
def memPairs (mem : Nat → OByte) : List (Nat × Slot) → Option (List (Slot × WExpr))
  | [] => some []
  | (o, s) :: rest =>
    match memWord mem o, memPairs mem rest with
    | some e, some ps => some ((s, e) :: ps)
    | _, _ => none

/-- The values an arrival's writes hold in the template's write slots, when its writes are to the
template's keys, in its order. -/
def writePairs : Writes → List (WExpr × Slot) → Option (List (Slot × WExpr))
  | [], [] => some []
  | (k, e) :: ws, (k', s) :: cs =>
    if k = k' then (writePairs ws cs).map ((s, e) :: ·) else none
  | _, _ => none

/-- The words an arrival holds in the template's slots. -/
def leafPairs (C : Cut) (senv : SEnv) (st : SState) : Option (List (Slot × WExpr)) :=
  match idPairs senv C.ids, memPairs st.mem C.mem, writePairs st.writes C.writes with
  | some a, some b, some c => some (a ++ b ++ c)
  | _, _, _ => none

/-- The header words of an arrival: the first word each holds. -/
def hwOf (nhw : Nat) (ps : List (Slot × WExpr)) : List WExpr :=
  (List.range nhw).map fun k => ((ps.find? (fun p => decide (p.1 = .hw k))).map Prod.snd).getD (.lit 0)

/-- **Match an arrival against the template**: its header words, when every slot holds its word,
nothing outside the template was written, and there are no logs. -/
def Cut.matchLeaf (C : Cut) (n : Nat) (senv : SEnv) (st : SState) (D MO : List Nat) :
    Option (List WExpr) :=
  match leafPairs C senv st with
  | none => none
  | some ps =>
    if (ps.all (fun p => slotOk n (hwOf C.nhw ps) p.1 p.2) && C.writes.all (fun w => argsBelow n w.1) && D.all (fun j => decide (j ∈ C.ids.map Prod.fst)) &&
        MO.all (fun o => decide (o ∈ C.mem.map Prod.fst)) && st.logs.isEmpty) = true then
      some (hwOf C.nhw ps)
    else none

/-- A leaf of a run: an end's tree, or an arrival at the header with its header words. -/
inductive Out where
  | exit (T : Tree)
  | back (hs : List WExpr)
  deriving DecidableEq, Repr

/-- The certificate's header block. -/
def Cut.header (C : Cut) (m : Module) : Option Block :=
  match m.functions[C.fn]? with
  | some f => f.blocks[C.head]?
  | none => none

/-- **The leaves of a run**, each with the sides of the words it branched on: an arrival's
header words after the header's phis, matched against the template. -/
def CTree.leaves (C : Cut) (n : Nat) (blk : Block) : Facts → CTree → Option (List (Facts × Out))
  | path, .done T => some [(path, .exit T)]
  | path, .back pred senv st D MO =>
    match symPhis senv pred blk.phis senv with
    | none => none
    | some senv1 =>
      match C.matchLeaf n senv1 st (D ++ blk.phis.map Prod.fst) MO with
      | some hs => some [(path, .back hs)]
      | none => none
  | path, .ite e t f =>
    match CTree.leaves C n blk ((e, true) :: path) t, CTree.leaves C n blk ((e, false) :: path) f with
    | some a, some b => some (a ++ b)
    | _, _ => none

/-- The memory words the module's entry writes before its first block. -/
def entryMO (m : Module) : List Nat :=
  match m.functions[m.entry]? with
  | some f => match f.entryHeap with | some _ => [64] | none => []
  | none => []

/-- The leaves of the iteration runs, one run per case: from the template after the header's phis,
under the case's facts. -/
def iterLeaves (C : Cut) (ev : EnvFlags) (m : Module) (sel n : Nat) (blk : Block) :
    List Facts → Option (List (Facts × Out))
  | [] => some []
  | F :: Fs =>
    match cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.resume C.fn C.head blk.insts blk.term)
        (C.env n) (C.st n) F (C.ids.map Prod.fst) (C.mem.map Prod.fst), iterLeaves C ev m sel n blk Fs with
    | some B, some rest => (B.leaves C n blk F).map (· ++ rest)
    | _, _ => none

/-- **The check**: the entry run from the module's entry and the iteration runs from the template
after the header's phis, one under each case's facts, each with its arrivals matched; the leaves of
the entry run and of all iteration runs. -/
def Cut.check (C : Cut) (ev : EnvFlags) (m : Module) (sel n : Nat) :
    Option (List (Facts × Out) × List (Facts × Out)) :=
  match C.header m with
  | none => none
  | some blk =>
    match cutRun ev (.w (.lit 0)) m sel n C.fn C.head C.fuel (.enter m.entry 0 0) (fun _ => .w (.lit 0))
        (symEntryStart m SState.initial) [] [] (entryMO m), iterLeaves C ev m sel n blk C.cases with
    | some E, some li =>
      match E.leaves C n blk [] with
      | some le => some (le, li)
      | none => none
    | _, _ => none

/-! ## Header valuations and the obligations -/

/-- The header valuation an arrival gives: the call's words, then its header words. -/
def nextVal (n : Nat) (σ : Val) (hs : List WExpr) : Val :=
  { σ with args := σ.args.take n ++ hs.map (·.eval σ) }

/-- The call's valuation under a header valuation: its first `n` words. -/
def trunc (n : Nat) (σ : Val) : Val := { σ with args := σ.args.take n }

/-- **The obligations of the leaves**, over header valuations: the source loop's record `L ρ` of
the call's valuation `ρ`, read at `toSrc σ` (its invariant at the first arrival, one
`LoopRecord.Step` per back edge, so its measure falls), a MIR-only invariant `X` (what the
compiler keeps beside the loop's words), some case's facts at every header valuation, and every end
the tree `T` of the call, on every call valuation `A` admits. -/
structure Obl (L : Val → LoopRecord) (toSrc : Val → Val) (X : Val → Prop) (A : Val → Prop) (n : Nat)
    (cases : List Facts) (T : Tree) (le li : List (Facts × Out)) : Prop where
  entry : ∀ ρ : Val, ρ.args.length = n → ρ.Ok → A ρ → ∀ p ∈ le, p.1.Hold ρ →
    match p.2 with
    | .exit T' => (T'.eval ρ).obs = (T.eval ρ).obs
    | .back hs => (L ρ).P (toSrc (nextVal n ρ hs)) ∧ X (nextVal n ρ hs)
  iter : ∀ σ : Val, n ≤ σ.args.length → σ.Ok → A (trunc n σ) → (L (trunc n σ)).P (toSrc σ) → X σ →
    ∀ p ∈ li, p.1.Hold σ →
    match p.2 with
    | .exit T' => (T'.eval σ).obs = (T.eval (trunc n σ)).obs
    | .back hs => (L (trunc n σ)).Step (toSrc σ) (toSrc (nextVal n σ hs)) ∧ X (nextVal n σ hs)
  facts : ∀ σ : Val, n ≤ σ.args.length → σ.Ok → A (trunc n σ) → (L (trunc n σ)).P (toSrc σ) → X σ →
    ∃ F ∈ cases, F.Hold σ

end Verify.LoopSource.Equiv
