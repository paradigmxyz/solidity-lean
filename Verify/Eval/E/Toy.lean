import Verify.Eval.Common.Measure

/-!
# Lane E: an EVM-shaped toy machine for proof-shape experiments

A pure-Lean copy of the shape of EthLib's program logic (Logic/Triple.lean, Logic/Steps.lean,
Logic/NatCode.lean), small enough to build in seconds, so that the experiments of lane E
(docs/eval/e.md) measure the SHAPE of a proof (shared helpers, shared block continuations,
balanced composition, frames behind definitions) rather than the cost of one tactic.

What it keeps from EthLib:

* code stored as one number n of size bytes, a byte being one shift (byteAt), so that a
  fact about a byte costs the same at every position and is closed by kernel evaluation on
  big numbers, as evm_code does;
* jump destinations valid by a walk along the opcodes from 0 (walk), checked by
  decide +kernel (evm_dest), whose cost grows with the destination;
* frames named by a predicate At pc stack gas, rules that are Hoare triples between them,
  Triple.seq to compose them and Spec for a run that stops;
* symbolic words ((x + y) % 2^256) and symbolic gas g - c with a gas bound by omega.
-/

namespace Verify.Eval.E.Toy

/-- A frame: program counter, stack, gas, and whether it still runs. -/
structure St where
  pc : Nat
  stk : List Nat
  gas : Nat
  running : Bool

/-- The byte at i of the code of size bytes stored big-endian in n, 0 past its end. -/
def byteAt (n size i : Nat) : Nat := if i < size then (n >>> (8 * (size - 1 - i))) % 256 else 0

/-- The position of the opcode after the one at pc, past a PUSH1's data. -/
def nextPc (n size pc : Nat) : Nat := if byteAt n size pc = 0x60 then pc + 2 else pc + 1

/-- Whether the opcodes from pc reach target in at most fuel opcodes. -/
def walk (n size : Nat) : (fuel pc target : Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, pc, target =>
    if pc = target then true
    else if pc < target then walk n size fuel (nextPc n size pc) target else false

/-- A valid jump destination: an opcode boundary that holds JUMPDEST. -/
def valid (n size d : Nat) : Bool := walk n size size 0 d && byteAt n size d == 0x5b

/-- The word size. -/
abbrev W : Nat := 2 ^ 256

/-- One step of the code n of size bytes. -/
inductive Step (n size : Nat) : St → St → Prop
  | push1 {pc stk gas} : byteAt n size pc = 0x60 → 3 ≤ gas →
      Step n size ⟨pc, stk, gas, true⟩ ⟨pc + 2, byteAt n size (pc + 1) :: stk, gas - 3, true⟩
  | add {pc x y r gas} : byteAt n size pc = 0x01 → 3 ≤ gas →
      Step n size ⟨pc, x :: y :: r, gas, true⟩ ⟨pc + 1, (x + y) % W :: r, gas - 3, true⟩
  | mul {pc x y r gas} : byteAt n size pc = 0x02 → 5 ≤ gas →
      Step n size ⟨pc, x :: y :: r, gas, true⟩ ⟨pc + 1, (x * y) % W :: r, gas - 5, true⟩
  | pop {pc x r gas} : byteAt n size pc = 0x50 → 2 ≤ gas →
      Step n size ⟨pc, x :: r, gas, true⟩ ⟨pc + 1, r, gas - 2, true⟩
  | dup1 {pc x r gas} : byteAt n size pc = 0x80 → 3 ≤ gas →
      Step n size ⟨pc, x :: r, gas, true⟩ ⟨pc + 1, x :: x :: r, gas - 3, true⟩
  | swap1 {pc x y r gas} : byteAt n size pc = 0x90 → 3 ≤ gas →
      Step n size ⟨pc, x :: y :: r, gas, true⟩ ⟨pc + 1, y :: x :: r, gas - 3, true⟩
  | jumpdest {pc stk gas} : byteAt n size pc = 0x5b → 1 ≤ gas →
      Step n size ⟨pc, stk, gas, true⟩ ⟨pc + 1, stk, gas - 1, true⟩
  | jump {pc d r gas} : byteAt n size pc = 0x56 → 8 ≤ gas → valid n size d = true →
      Step n size ⟨pc, d :: r, gas, true⟩ ⟨d, r, gas - 8, true⟩
  | jumpiTaken {pc d c r gas} : byteAt n size pc = 0x57 → 10 ≤ gas → c ≠ 0 →
      valid n size d = true → Step n size ⟨pc, d :: c :: r, gas, true⟩ ⟨d, r, gas - 10, true⟩
  | jumpiSkip {pc d c r gas} : byteAt n size pc = 0x57 → 10 ≤ gas → c = 0 →
      Step n size ⟨pc, d :: c :: r, gas, true⟩ ⟨pc + 1, r, gas - 10, true⟩
  | eq {pc x y r gas} : byteAt n size pc = 0x14 → 3 ≤ gas →
      Step n size ⟨pc, x :: y :: r, gas, true⟩ ⟨pc + 1, (if x = y then 1 else 0) :: r, gas - 3, true⟩
  | stop {pc stk gas} : byteAt n size pc = 0x00 →
      Step n size ⟨pc, stk, gas, true⟩ ⟨pc, stk, gas, false⟩

/-- The steps from a reach b. -/
inductive Reaches (S : St → St → Prop) : St → St → Prop
  | refl (a) : Reaches S a a
  | head {a b c} : S a b → Reaches S b c → Reaches S a c

theorem Reaches.trans {S : St → St → Prop} {a b c : St} (h₁ : Reaches S a b)
    (h₂ : Reaches S b c) : Reaches S a c := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

/-- From every frame of P, the steps reach a frame of Q (EthLib's Triple). -/
def Triple (S : St → St → Prop) (P Q : St → Prop) : Prop :=
  ∀ s, P s → ∃ t, Reaches S s t ∧ Q t

theorem Triple.seq {S : St → St → Prop} {P Q R : St → Prop} (first : Triple S P Q)
    (second : Triple S Q R) : Triple S P R := fun s hp =>
  let ⟨m, h₁, hq⟩ := first s hp
  let ⟨t, h₂, hr⟩ := second m hq
  ⟨t, h₁.trans h₂, hr⟩

theorem Triple.of_step {S : St → St → Prop} {P Q : St → Prop}
    (h : ∀ s, P s → ∃ t, S s t ∧ Q t) : Triple S P Q := fun s hp =>
  let ⟨t, hs, hq⟩ := h s hp
  ⟨t, .head hs (.refl t), hq⟩

theorem Triple.refl {S : St → St → Prop} {P : St → Prop} : Triple S P P := fun s hp =>
  ⟨s, .refl s, hp⟩

/-- A run that stops in a frame of Q (EthLib's Spec). -/
def Spec (n size : Nat) (P Q : St → Prop) : Prop :=
  Triple (Step n size) P fun s => s.running = false ∧ Q s

theorem Spec.seq {n size : Nat} {P Q R : St → Prop} (first : Triple (Step n size) P Q)
    (second : Spec n size Q R) : Spec n size P R := Triple.seq first second

/-- The frame at pc with stk and gas, running (EthLib's At). -/
def At (pc : Nat) (stk : List Nat) (gas : Nat) (s : St) : Prop := s = ⟨pc, stk, gas, true⟩

/-! ## Rules, one per opcode

Each rule names the frame after the step with its own program counter, gas and pushed word,
and asks for the equations that tie them to the frame before (closed by rfl and omega), as a
generator that knows the program emits the next frame in normal form (EthLib's evm_tidy). -/

section Rules
variable {n size pc pc' gas gas' : Nat}

theorem r_push1 {stk : List Nat} {w : Nat} (hb : byteAt n size pc = 0x60) (hp : pc' = pc + 2)
    (hw : byteAt n size (pc + 1) = w) (hg : 3 ≤ gas) (he : gas' = gas - 3) :
    Triple (Step n size) (At pc stk gas) (At pc' (w :: stk) gas') :=
  Triple.of_step fun s hs => by subst hs hp hw he; exact ⟨_, .push1 hb hg, rfl⟩

theorem r_add {x y : Nat} {r : List Nat} (hb : byteAt n size pc = 0x01) (hp : pc' = pc + 1)
    (hg : 3 ≤ gas) (he : gas' = gas - 3) :
    Triple (Step n size) (At pc (x :: y :: r) gas) (At pc' ((x + y) % W :: r) gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .add hb hg, rfl⟩

theorem r_mul {x y : Nat} {r : List Nat} (hb : byteAt n size pc = 0x02) (hp : pc' = pc + 1)
    (hg : 5 ≤ gas) (he : gas' = gas - 5) :
    Triple (Step n size) (At pc (x :: y :: r) gas) (At pc' ((x * y) % W :: r) gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .mul hb hg, rfl⟩

theorem r_eq {x y w : Nat} {r : List Nat} (hb : byteAt n size pc = 0x14) (hp : pc' = pc + 1)
    (hw : (if x = y then 1 else 0) = w) (hg : 3 ≤ gas) (he : gas' = gas - 3) :
    Triple (Step n size) (At pc (x :: y :: r) gas) (At pc' (w :: r) gas') :=
  Triple.of_step fun s hs => by subst hs hp hw he; exact ⟨_, .eq hb hg, rfl⟩

theorem r_pop {x : Nat} {r : List Nat} (hb : byteAt n size pc = 0x50) (hp : pc' = pc + 1)
    (hg : 2 ≤ gas) (he : gas' = gas - 2) :
    Triple (Step n size) (At pc (x :: r) gas) (At pc' r gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .pop hb hg, rfl⟩

theorem r_dup1 {x : Nat} {r : List Nat} (hb : byteAt n size pc = 0x80) (hp : pc' = pc + 1)
    (hg : 3 ≤ gas) (he : gas' = gas - 3) :
    Triple (Step n size) (At pc (x :: r) gas) (At pc' (x :: x :: r) gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .dup1 hb hg, rfl⟩

theorem r_swap1 {x y : Nat} {r : List Nat} (hb : byteAt n size pc = 0x90) (hp : pc' = pc + 1)
    (hg : 3 ≤ gas) (he : gas' = gas - 3) :
    Triple (Step n size) (At pc (x :: y :: r) gas) (At pc' (y :: x :: r) gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .swap1 hb hg, rfl⟩

theorem r_jumpdest {stk : List Nat} (hb : byteAt n size pc = 0x5b) (hp : pc' = pc + 1)
    (hg : 1 ≤ gas) (he : gas' = gas - 1) :
    Triple (Step n size) (At pc stk gas) (At pc' stk gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .jumpdest hb hg, rfl⟩

theorem r_jump {d : Nat} {r : List Nat} (hb : byteAt n size pc = 0x56) (hg : 8 ≤ gas)
    (he : gas' = gas - 8) (hv : valid n size d = true) :
    Triple (Step n size) (At pc (d :: r) gas) (At d r gas') :=
  Triple.of_step fun s hs => by subst hs he; exact ⟨_, .jump hb hg hv, rfl⟩

theorem r_jumpiTaken {d k : Nat} {r : List Nat} (hb : byteAt n size pc = 0x57)
    (hg : 10 ≤ gas) (he : gas' = gas - 10) (hk : k ≠ 0) (hv : valid n size d = true) :
    Triple (Step n size) (At pc (d :: k :: r) gas) (At d r gas') :=
  Triple.of_step fun s hs => by subst hs he; exact ⟨_, .jumpiTaken hb hg hk hv, rfl⟩

theorem r_jumpiSkip {d k : Nat} {r : List Nat} (hb : byteAt n size pc = 0x57)
    (hp : pc' = pc + 1) (hg : 10 ≤ gas) (he : gas' = gas - 10) (hk : k = 0) :
    Triple (Step n size) (At pc (d :: k :: r) gas) (At pc' r gas') :=
  Triple.of_step fun s hs => by subst hs hp he; exact ⟨_, .jumpiSkip hb hg hk, rfl⟩

theorem r_stop {stk : List Nat} (hb : byteAt n size pc = 0x00) :
    Spec n size (At pc stk gas) (fun _ => True) := fun s hs => by
  subst hs; exact ⟨_, .head (.stop hb) (.refl _), rfl, trivial⟩

end Rules

end Verify.Eval.E.Toy
