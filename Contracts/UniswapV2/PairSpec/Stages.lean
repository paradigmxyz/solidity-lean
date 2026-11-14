import Contracts.UniswapV2.PairSpec.Statement

/-!
# UniswapV2Pair: the stage theorems the published statement composes

These are the statements of the theorems the backend lanes produce, as `Prop`s, so that the
composition (Published.lean) is kernel-checked now and becomes the published theorem by applying
it to the lanes' theorems once they land. None is assumed anywhere: each is a hypothesis of
`published_of_stages`, visible in its statement. Names (RESULT.md lists them):

| Prop | the theorem that will prove it | lane |
|---|---|---|
| `EquivSwap`, `EquivSkim`, `EquivSync` | `SolarTV.Export.UniswapV2Pair.Ctx.equiv_swap` / `_skim` / `_sync` | pair-stages-b |
| `TermSwap`, `TermSkim`, `TermSync` | `SolidCore.Spec.UniswapV2.Pair.terminates_swap` / `_skim` / `_sync` | pair-stages-b |
| `MeetsSwap`, `MeetsSkim`, `MeetsSync` | `SolidCore.Spec.UniswapV2.Pair.swap_holds` / `skim_holds` / `sync_holds` | pair-spec (spec connection) |

pair-stages-a's mint and burn enter the same way (`EquivMint`, ...) once their ghost step is
written; the statement does not cover them yet.
-/

namespace SolidCore.Spec.UniswapV2.PairSpec.Stages

open SolarTV SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec.UniswapV2.PairSpec

/-- Equivalence on the calls `V` of one function: every result of the exact bytes in every admitted
environment, at every gas below `2 ^ 256`, is the checked source's in some admitted world, or an
inert failure, or explained only by a wide world that is not admitted (`Unadmitted`). -/
def EquivOn (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : Call → Prop) : Prop :=
  ∀ env, EnvOk env → ∀ gas, gas < 2 ^ 256 → ∀ call, V call → ∀ obs,
    Target.runWithIn env gas code call = some obs →
      (∃ W, Admit W ∧ Source.runIn W SolidCore.Verify.VC.UniswapV2Pair.fuel c call = some obs) ∨
        Inert call obs ∨ Unadmitted SolidCore.Verify.VC.UniswapV2Pair.fuel c Wide Admit call obs

/-- Termination on the calls `V` of one function, with an allowed status, in every admitted world. -/
def TermOn (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : Call → Prop) : Prop :=
  ∀ W, Admit W → ∀ call, V call →
    ∃ obs, Source.runIn W SolidCore.Verify.VC.UniswapV2Pair.fuel c call = some obs ∧ Allowed W call obs

/-- The specification on the calls `V` of one function, in every admitted world, under the named
premise. -/
def MeetsOn (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : Call → Prop) : Prop :=
  HashScope → ∀ W, Admit W → Meets (solidCoreIn W SolidCore.Verify.VC.UniswapV2Pair.fuel) c V (Post W)

def EquivSwap (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := EquivOn c ValidSwap
def EquivSkim (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := EquivOn c ValidSkim
def EquivSync (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := EquivOn c ValidSync
def TermSwap (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := TermOn c ValidSwap
def TermSkim (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := TermOn c ValidSkim
def TermSync (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := TermOn c ValidSync
def MeetsSwap (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := MeetsOn c ValidSwap
def MeetsSkim (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := MeetsOn c ValidSkim
def MeetsSync (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop := MeetsOn c ValidSync

theorem EquivOn.or {c : SolidCore.Solidity.TypeCheck.CheckedContract} {V V' : Call → Prop}
    (h : EquivOn c V) (h' : EquivOn c V') : EquivOn c (fun call => V call ∨ V' call) := by
  intro env he gas hg call hc obs hr
  rcases hc with hc | hc
  · exact h env he gas hg call hc obs hr
  · exact h' env he gas hg call hc obs hr

theorem TermOn.or {c : SolidCore.Solidity.TypeCheck.CheckedContract} {V V' : Call → Prop}
    (h : TermOn c V) (h' : TermOn c V') : TermOn c (fun call => V call ∨ V' call) := by
  intro W hW call hc
  rcases hc with hc | hc
  · exact h W hW call hc
  · exact h' W hW call hc

theorem MeetsOn.or {c : SolidCore.Solidity.TypeCheck.CheckedContract} {V V' : Call → Prop}
    (h : MeetsOn c V) (h' : MeetsOn c V') : MeetsOn c (fun call => V call ∨ V' call) := by
  intro hk W hW call hc obs hr
  rcases hc with hc | hc
  · exact h hk W hW call hc obs hr
  · exact h' hk W hW call hc obs hr

end SolidCore.Spec.UniswapV2.PairSpec.Stages

