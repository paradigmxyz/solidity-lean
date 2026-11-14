import Verify.Final

/-!
# The shape of a certified compilation

What a published certificate of a contract states, as four separate obligations over SolidCore's
checked source `p` (in a source semantics `S`) and the exact emitted runtime bytecode `code`
(under EthLib at an explicit gas), on a declared valid-call precondition `Valid`:

* `Equiv` (behavioural equivalence, gas-insensitive): at every gas below `2 ^ 256`, every result
  of the bytecode on a valid call is the source's result on that call, or a failure that changes
  nothing (`Inert`: running out of gas is one). This is the backward simulation; the forward one is
  `Resources`, so together they give equality of observable results (`Certified.agree`).
* `Terminates`: the source halts on every valid call, with a status the specification allows
  (`Allowed`: success, or one of the declared reverts; an arbitrary revert is not allowed unless
  `Allowed` says so). For a fuel-indexed source (`solidCore fuel`) halting is within the fuel;
  for loops, the fuel bound is what a ranking certificate proves.
* `Meets`: the user specification `Post` holds of every source result on a valid call, over the
  same source semantics the other obligations use.
* `Resources`: an explicit gas bound `G call` below `2 ^ 64` from which on, at every gas below
  `2 ^ 256`, the bytecode gives exactly the source's result: it does not run out of gas. It is
  not a premise: `G` is part of the statement and the theorem must prove the run at every gas
  above it.

`Certified` is all four plus a witness that `Valid` is inhabited. Named environment
assumptions are hypotheses of the published statement (`Env → Certified …`), never folded into
`Valid`. A source that diverges or gets stuck on a valid call cannot meet `Terminates`, so it
never reaches the strongest status; stages of such programs keep the bidirectional
`SolarTV.CutPoint.LayerSim` (`ends_iff`, `diverges_iff`, `stuck_iff`), which this file does not
use, since for a source total on `Valid` a forward stage and the backward `Within` suffice
(`equiv_of_runs`, `resources_of_forward`).

Observables do not tell running out of gas from a revert with the same (empty) data, so
`Resources` asks for the source's exact result rather than "not out of gas".
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final

/-- A failure that changes nothing. -/
def Inert (call : Call) (obs : Observable) : Prop :=
  obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []

/-- **(1) Behavioural equivalence, gas-insensitive.** -/
def Equiv (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop) : Prop :=
  ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs, Final.Target.runWith gas code call = some obs →
    S.run p call = some obs ∨ Inert call obs

/-- **(2) Termination** of the source on every valid call, with an allowed status. -/
def Terminates (S : Sem) (p : S.Prog) (Valid : Call → Prop)
    (Allowed : Call → Observable → Prop) : Prop :=
  ∀ call, Valid call → ∃ obs, S.run p call = some obs ∧ Allowed call obs

/-- **(3) The specification** of every source result on a valid call. -/
def Meets (S : Sem) (p : S.Prog) (Valid : Call → Prop) (Post : Call → Observable → Prop) : Prop :=
  ∀ call, Valid call → ∀ obs, S.run p call = some obs → Post call obs

/-- **(4) Resources**: from `G call` gas on the bytecode gives the source's result exactly. -/
def Resources (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop)
    (G : Call → Nat) : Prop :=
  ∀ call, Valid call → G call < 2 ^ 64 ∧
    ∀ gas, G call ≤ gas → gas < 2 ^ 256 → Final.Target.runWith gas code call = S.run p call

/-- **The strongest status**: all four obligations on an inhabited precondition. -/
structure Certified (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop)
    (Allowed Post : Call → Observable → Prop) (G : Call → Nat) : Prop where
  inhabited : ∃ call, Valid call
  equiv : Equiv S p code Valid
  terminates : Terminates S p Valid Allowed
  meets : Meets S p Valid Post
  resources : Resources S p code Valid G

/-- Everything but resources: what a contract whose gas bound is not proved yet can state. Never
reported as the strongest status. -/
structure Functional (S : Sem) (p : S.Prog) (code : ByteArray) (Valid : Call → Prop)
    (Allowed Post : Call → Observable → Prop) : Prop where
  inhabited : ∃ call, Valid call
  equiv : Equiv S p code Valid
  terminates : Terminates S p Valid Allowed
  meets : Meets S p Valid Post

theorem Certified.functional {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified S p code Valid Allowed Post G) : Functional S p code Valid Allowed Post :=
  ⟨h.inhabited, h.equiv, h.terminates, h.meets⟩

/-! ## What the bytecode does -/

/-- **Total correctness of the bytecode.** At every gas from the bound on, every valid call ends,
with an allowed status, meeting the specification, with the source's observable. -/
theorem Certified.bytecode_total {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified S p code Valid Allowed Post G) (call : Call) (hc : Valid call) :
    G call < 2 ^ 64 ∧ ∀ gas, G call ≤ gas → gas < 2 ^ 256 → ∃ obs,
      Final.Target.runWith gas code call = some obs ∧ S.run p call = some obs ∧
        Allowed call obs ∧ Post call obs := by
  obtain ⟨hG, hrun⟩ := h.resources call hc
  refine ⟨hG, fun gas h1 h2 => ?_⟩
  obtain ⟨obs, hs, ha⟩ := h.terminates call hc
  exact ⟨obs, (hrun gas h1 h2).trans hs, hs, ha, h.meets call hc obs hs⟩

/-- **Partial correctness of the bytecode at every gas.** Every result of the bytecode on a valid
call, at any gas below `2 ^ 256`, is an allowed one meeting the specification, or a failure that
changes nothing. -/
theorem Functional.bytecode_any {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop}
    (h : Functional S p code Valid Allowed Post) (gas : Nat) (hg : gas < 2 ^ 256) (call : Call)
    (hc : Valid call) (obs : Observable) (hrun : Final.Target.runWith gas code call = some obs) :
    (Allowed call obs ∧ Post call obs) ∨ Inert call obs := by
  rcases h.equiv gas hg call hc obs hrun with e | e
  · obtain ⟨obs', hs, ha⟩ := h.terminates call hc
    obtain rfl : obs' = obs := Option.some.inj (hs.symm.trans e)
    exact Or.inl ⟨ha, h.meets call hc obs' hs⟩
  · exact Or.inr e

/-- Equivalence in both directions at enough gas: source and bytecode give the same observable. -/
theorem Certified.agree {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified S p code Valid Allowed Post G) (call : Call) (hc : Valid call) (gas : Nat)
    (h1 : G call ≤ gas) (h2 : gas < 2 ^ 256) :
    ∃ obs, S.run p call = some obs ∧ Final.Target.runWith gas code call = some obs := by
  obtain ⟨-, hr⟩ := h.bytecode_total call hc
  obtain ⟨obs, ht, hs, -⟩ := hr gas h1 h2
  exact ⟨obs, hs, ht⟩

/-! ## Composition from the existing pieces -/

/-- **Equivalence from a total source, forward stages and the per-run assembly theorem.** A
source that ends on every valid call, a stage from it into the EVM IR under every oracle meeting
`Ok`, and the assembly checker's per-run theorem (`AssembleCut.WithinRunLt`, unfolded) give
equivalence with the exact bytecode at every gas. -/
theorem equiv_of_runs {O : Type} {S : Sem} {p : S.Prog} {sem : O → Sem} {q : ∀ o, (sem o).Prog}
    {code : ByteArray} {Valid : Call → Prop} {Ok : O → Prop}
    (total : ∀ call, Valid call → ∃ obs, S.run p call = some obs)
    (stage : ∀ o, Ok o → Stage S (sem o) p (q o) Valid)
    (runs : ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∃ o, Ok o ∧
      Within (sem o) (ethLibWith gas) (q o) code (· = call)) :
    Equiv S p code Valid := by
  intro gas hg call hc obs hrun
  obtain ⟨o, ho, hw⟩ := runs gas hg call hc
  rcases hw call rfl obs hrun with e | e
  · obtain ⟨obs0, h0⟩ := total call hc
    have hq := stage o ho call hc obs0 h0
    obtain rfl : obs0 = obs := Option.some.inj (hq.symm.trans e)
    exact Or.inl h0
  · exact Or.inr e

/-- **Resources from a forward assembly theorem with gas.** -/
theorem resources_of_forward {S B : Sem} {p : S.Prog} {q : B.Prog} {code : ByteArray}
    {Valid : Call → Prop} {G : Call → Nat}
    (total : ∀ call, Valid call → ∃ obs, S.run p call = some obs)
    (stage : Stage S B p q Valid)
    (forward : ∀ call, Valid call → G call < 2 ^ 64 ∧ ∀ gas, G call ≤ gas → gas < 2 ^ 256 →
      ∀ obs, B.run q call = some obs → Final.Target.runWith gas code call = some obs) :
    Resources S p code Valid G := by
  intro call hc
  obtain ⟨hG, hf⟩ := forward call hc
  refine ⟨hG, fun gas h1 h2 => ?_⟩
  obtain ⟨obs, hs⟩ := total call hc
  rw [hs]
  exact hf gas h1 h2 obs (stage call hc obs hs)

/-- Termination from a source that ends with an allowed status. -/
theorem terminates_of {S : Sem} {p : S.Prog} {Valid : Call → Prop}
    {Allowed : Call → Observable → Prop} (f : Call → Observable)
    (run : ∀ call, Valid call → S.run p call = some (f call))
    (allowed : ∀ call, Valid call → Allowed call (f call)) : Terminates S p Valid Allowed :=
  fun call hc => ⟨f call, run call hc, allowed call hc⟩

/-- solar-verify's contract specification as a postcondition: a result of a call of a specified
function, on clean argument words, with a value below `2 ^ 256`, from a storage that meets the
invariant and the precondition, meets `ContractSpec.Outcome`. -/
def specPost {St : Type} (spec : ContractSpec St) (call : Call) (obs : Observable) : Prop :=
  ∀ f ∈ spec.fns, ∀ args, f.Typed args → ∀ v, v < 2 ^ 256 → ∀ σ, call = f.call args v σ →
    spec.invariant (spec.abs (slotValue σ)) → f.requires args (spec.abs (slotValue σ)) →
      spec.Outcome f args call obs

/-- `Holds` of the source is `Meets` of `specPost`. -/
theorem meets_of_holds {St : Type} {S : Sem} {p : S.Prog} {spec : ContractSpec St}
    {Valid : Call → Prop} (h : Holds S p spec) : Meets S p Valid (specPost spec) := by
  intro call _ obs hrun f hf args ht v hv σ he hinv hreq
  subst he
  exact h f hf args ht v hv σ hinv hreq obs hrun

/-! ## Negative controls: each obligation fails by a concrete mismatch -/

theorem not_equiv_of {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {call : Call} {gas : Nat} {obs : Observable} (hc : Valid call) (hg : gas < 2 ^ 256)
    (hrun : Final.Target.runWith gas code call = some obs) (hs : S.run p call ≠ some obs)
    (hi : ¬Inert call obs) : ¬Equiv S p code Valid := fun h =>
  (h gas hg call hc obs hrun).elim hs hi

theorem not_terminates_of_none {S : Sem} {p : S.Prog} {Valid : Call → Prop}
    {Allowed : Call → Observable → Prop} {call : Call} (hc : Valid call)
    (hn : S.run p call = none) : ¬Terminates S p Valid Allowed := fun h => by
  obtain ⟨obs, hs, -⟩ := h call hc
  rw [hn] at hs
  cases hs

theorem not_terminates_of_disallowed {S : Sem} {p : S.Prog} {Valid : Call → Prop}
    {Allowed : Call → Observable → Prop} {call : Call} {obs : Observable} (hc : Valid call)
    (hs : S.run p call = some obs) (hn : ¬Allowed call obs) : ¬Terminates S p Valid Allowed :=
  fun h => by
  obtain ⟨obs', hs', ha⟩ := h call hc
  rw [hs] at hs'
  cases hs'
  exact hn ha

theorem not_meets_of {S : Sem} {p : S.Prog} {Valid : Call → Prop}
    {Post : Call → Observable → Prop} {call : Call} {obs : Observable} (hc : Valid call)
    (hs : S.run p call = some obs) (hn : ¬Post call obs) : ¬Meets S p Valid Post :=
  fun h => hn (h call hc obs hs)

theorem not_resources_of {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} {call : Call} {gas : Nat} (hc : Valid call) (h1 : G call ≤ gas)
    (h2 : gas < 2 ^ 256) (hn : Final.Target.runWith gas code call ≠ S.run p call) :
    ¬Resources S p code Valid G := fun h => hn ((h call hc).2 gas h1 h2)

theorem not_resources_of_bound {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {G : Call → Nat} {call : Call} (hc : Valid call) (hG : 2 ^ 64 ≤ G call) :
    ¬Resources S p code Valid G := fun h => absurd (h call hc).1 (Nat.not_lt.mpr hG)

theorem not_certified_of_empty {S : Sem} {p : S.Prog} {code : ByteArray} {Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} {G : Call → Nat} (he : ∀ call, ¬Valid call) :
    ¬Certified S p code Valid Allowed Post G := fun h => by
  obtain ⟨call, hc⟩ := h.inhabited
  exact he call hc

/-- info: 'SolidCore.Refinement.Shapes.Certified.bytecode_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Certified.bytecode_total

end SolidCore.Refinement.Shapes
