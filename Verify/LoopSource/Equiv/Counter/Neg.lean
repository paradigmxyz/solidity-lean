import Verify.LoopSource.Equiv.Counter.Obl

/-!
# Counter's loop obligations fail closed under mutation

Each negative changes one input of \`Counter.bump\`'s obligations and shows, in the kernel, that the
sequents the check emits for it cannot all be valid: one of them has a concrete counterexample
valuation (\`rejects_sound\`), so \`obl_of_seqs\` cannot apply.

* \`neg_measure\`: the measure \`count\` (header word 1, which grows each iteration) in place of \`μ\`;
* \`neg_swap\`: the MIR header's branch sides swapped (the loop's exit condition negated);
* \`neg_body\`: the source tree with the stored count one larger (a mutated loop body);
* \`neg_guard\`: the source tree with its first guard negated;
* \`neg_exit\`: the source tree with success and revert exchanged.

The source mutations change the loop-free tree \`T\` that the source loop runs to, which is what the
obligations compare the MIR's ends against.
-/

namespace Verify.LoopSource.Equiv.CounterNeg
open SolarTV SolarTV.MIR.Lowered SolidCore.Refinement.Generic Verify.LoopSource.Equiv
open Verify.LoopSource.Equiv.Inv Verify.LoopSource.Equiv.Generated.Counter Verify.LoopSource.Equiv.CounterObl

/-- Counter's MIR with the loop header's branch sides swapped. -/
def swapM : Module := setBlock SolarTV.Export.Counter.stage0 cut.fn cut.head fun blk =>
  { blk with term := match blk.term with | .branch c y n => .branch c n y | t => t }

/-- Counter's MIR with the count's step 2 while the loop counter steps 1 (unequal deltas). -/
def mDelta : Module := setBlock SolarTV.Export.Counter.stage0 4 3 fun blk =>
  { blk with insts := blk.insts.set 0 (.pure 38 .add [.value 48, .const 2]) }

/-- Counter's MIR with the loop counter starting at \`0 + n\` instead of \`0 - n\` (the sign of the
modular start, so the loop runs \`2 ^ 256 - n\` times). -/
def mSign : Module := setBlock SolarTV.Export.Counter.stage0 4 7 fun blk =>
  { blk with insts := [.pure 61 .add [.const 0, .value 55]] }

/-- Counter's MIR with the count entering the loop as 0 instead of the stored count (a wrong initial
binding). -/
def mInit : Module := setBlock SolarTV.Export.Counter.stage0 4 1 fun blk =>
  { blk with phis := blk.phis.map fun p =>
      if p.1 = 48 then (48, p.2.map fun a => if a.1 = 7 then (7, .const 0) else a) else p }

def mapLeaves (g : Bool → List OByte → Writes → List Log → Tree) : Tree → Tree
  | .halt ok o w l => g ok o w l
  | .ite c t e => .ite c (mapLeaves g t) (mapLeaves g e)

def Tbody : Tree := mapLeaves (fun ok o w l => .halt ok o (w.map fun p => (p.1, .bin .add p.2 (.lit 1))) l) T
def Tguard : Tree := match T with | .ite c t e => .ite (.un .iszero c) t e | t => t
def Texit : Tree := mapLeaves (fun ok o w l => .halt (!ok) o w l) T

/-- A valuation with argument words \`as\` and storage slots 0 and 1. -/
def val (as : List Nat) (s0 s1 : Nat) : Val :=
  { args := as, store := fun k => [s0, s1].getD k 0, hash := fun _ _ => 0, caller := 0 }

/-- A header valuation of an iteration: header word 1 (the count) is `2 ^ 256 - 1`. -/
def σw : Val := val [1, 2 ^ 256 - 1, 0, 0, 0, 0, 0, 0, 36, 0, 2 ^ 256 - 1, 0, 1, 0] 0 5

/-- A mutated MIR's obligations are refuted: on its check's leaves, sequent `i` fails at `σ`. -/
theorem rejects_check {m : Module} {T : Tree} {I : List F} {μ : WExpr} {σ : Val} {i : Nat}
    (hb : rejects σ i ((cut.check .off m 0xb20eb4c4 1).bind fun p => allSeqs 1 cut.cases T p.1 p.2 I μ) = true) :
    ∀ le' li', cut.check .off m 0xb20eb4c4 1 = some (le', li') →
      ∀ ss, allSeqs 1 cut.cases T le' li' I μ = some ss → ¬ ∀ s ∈ ss, s.Valid := by
  intro le' li' hc ss hs
  simp only [hc, Option.bind_some, hs] at hb
  exact rejects_sound hb

theorem neg_measure : ∀ ss, allSeqs 1 cut.cases T le li I (.arg 2) = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := σw) (i := 30) (h ▸ by decide +kernel)

theorem neg_swap : ∀ le' li', cut.check .off swapM 0xb20eb4c4 1 = some (le', li') →
    ∀ ss, allSeqs 1 cut.cases T le' li' I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  rejects_check (σ := val [0] 0 0) (i := 17) (by decide +kernel)

theorem neg_body : ∀ ss, allSeqs 1 cut.cases Tbody le li I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := val [1, 0, 1, 1, 1, 1, 0, 0, 36, 0, 2 ^ 256 - 1, 0, 1, 0] 0 5) (i := 32) (h ▸ by decide +kernel)

/-- A call valuation whose stored count is `2 ^ 256 - 2`. -/
def σg : Val := val [2] (2 ^ 256 - 2) 0

theorem neg_guard : ∀ ss, allSeqs 1 cut.cases Tguard le li I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := σg) (i := 24) (h ▸ by decide +kernel)

theorem neg_exit : ∀ ss, allSeqs 1 cut.cases Texit le li I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := σg) (i := 24) (h ▸ by decide +kernel)

theorem neg_delta : ∀ le' li', cut.check .off mDelta 0xb20eb4c4 1 = some (le', li') →
    ∀ ss, allSeqs 1 cut.cases T le' li' I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  rejects_check (σ := σw) (i := 17) (by decide +kernel)

theorem neg_sign : ∀ le' li', cut.check .off mSign 0xb20eb4c4 1 = some (le', li') →
    ∀ ss, allSeqs 1 cut.cases T le' li' I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  rejects_check (σ := val [1] 0 5) (i := 8) (by decide +kernel)

theorem neg_init : ∀ le' li', cut.check .off mInit 0xb20eb4c4 1 = some (le', li') →
    ∀ ss, allSeqs 1 cut.cases T le' li' I μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  rejects_check (σ := val [0] 5 5) (i := 16) (by decide +kernel)

/-- Truncating (natural number) subtraction from 0 in place of subtraction mod \`2 ^ 256\`: \`0 - x\`
is 0. -/
def wNatSub : WExpr → WExpr
  | .bin .sub (.lit 0) _ => .lit 0
  | .bin op a b => .bin op (wNatSub a) (wNatSub b)
  | .un op a => .un op (wNatSub a)
  | e => e

def fNatSub : F → F
  | .fact e b => .fact (wNatSub e) b
  | .le a b => .le (wNatSub a) (wNatSub b)
  | .lt a b => .lt (wNatSub a) (wNatSub b)
  | .eq a b => .eq (wNatSub a) (wNatSub b)
  | .lin a b c d => .lin (wNatSub a) (wNatSub b) (wNatSub c) (wNatSub d)
  | .or f g => .or (fNatSub f) (fNatSub g)
  | .not f => .not (fNatSub f)

/-- The invariant with Nat subtraction (3 of its 12 formulas change). -/
def INat : List F := I.map fNatSub

/-- **The invariant with Nat subtraction is rejected.** -/
theorem neg_natsub_inv : ∀ ss, allSeqs 1 cut.cases T le li INat μ = some ss → ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := val [1] 0 5) (i := 8) (h ▸ by decide +kernel)

/-- **The measure with Nat subtraction (\`0 - h\` truncated to 0) is rejected.** -/
theorem neg_natsub_measure : ∀ ss, allSeqs 1 cut.cases T le li I (wNatSub μ) = some ss →
    ¬ ∀ s ∈ ss, s.Valid :=
  fun ss h => rejects_sound (σ := σw) (i := 30) (h ▸ by decide +kernel)

end Verify.LoopSource.Equiv.CounterNeg

/-- info: 'Verify.LoopSource.Equiv.CounterNeg.neg_natsub_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterNeg.neg_natsub_inv

/-- info: 'Verify.LoopSource.Equiv.CounterNeg.neg_natsub_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterNeg.neg_natsub_measure
