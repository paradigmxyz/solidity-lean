# The generic certification interface

One statement certifies every supported contract. The driver never picks a statement shape, a
theorem name or a proof route by the contract's name: it writes the three parameters of
`SolidCore.Verify.Generic.Expected` and asks the kernel to check a proof of it over the exact bytes
it compiled.

```lean
-- Verify/Generic/Expected.lean
def Expected (src : Source) (spec : Spec) (bytes : List Nat) : Prop :=
  bytes.all (· < 256) = true ∧ spec.Covered ∧
    (spec.Assumed → ∀ ctx, spec.Contexts ctx → ∃ c, src.checked = .ok c ∧
      CertifiedAt (src.semAt ctx) c ctx (runtimeCode bytes) (spec.Valid ctx) (spec.Allowed ctx)
        (spec.Post ctx) (spec.gas ctx))
```

## Parameters

| Parameter | What it is | Who writes it |
|---|---|---|
| `src : Source` | `unit`: solc's AST of the source unit, imported by `scripts/solc_ast_to_lean_source.py`; `contract`: the contract's name; `fuel` | the driver, from the fresh solc AST |
| `spec : Spec` | `Contexts` (covered frames), `entries` (declared entrypoints and their calls), `Valid`, `Allowed`, `Post`, `gas` (each a function of the context), `assumptions` (named Props) | the reviewed spec module (solar-verify's export or a reviewed Lean term); the driver names it |
| `bytes : List Nat` | the runtime bytes solar emitted in this run, as numbers | the driver, from its own compile |

`src.checked` is SolidCore's type check of solc's AST. That independent source semantics is the
source of truth: solar's HIR and MIR appear only inside proofs, as stages checked against it, so a
solar parser, resolution or lowering bug shows up as a failed stage, never as a changed statement.

## What it states

1. **Bytes.** `bytes` are bytes; `runtimeCode bytes` is exactly them.
2. **Coverage (`Spec.Covered`), checked in the same context.** Some context is covered; every
   covered context is real (caller below `2^160`, not the contract); for every covered context and
   every declared entrypoint there is a valid call of that entrypoint in that context (no entry's
   premise is unsatisfiable); the postcondition rejects some result of a valid call; the allowed
   statuses reject some revert of a valid call.
3. **Certified in every covered context, under the named assumptions (`CertifiedAt`).** Two separate
   proofs composed on the same checked contract, context, semantics and valid calls:
   * `TranslationAt` (the source translation, no user spec): equivalence at every gas below
     `2^256` (every result of the bytes is the source's or a failure that changes nothing),
     termination of the source, and resources (`ResourcesAt`: from `gas ctx call < 2^64` on, the
     bytes' observable equals the source's);
   * `SpecProof` (the user spec, no bytes): every source result on a valid call has an allowed
     status and meets the postcondition.

## One parametric context

`Context` carries the caller, a parameter of both semantics (`solidCoreFrom` and
`Final.Target.runWithFrom`). The contract's address and the block and transaction are
`Target.message`'s fixed values, recorded as coverage. A statement for one caller sets
`Contexts := (· = Context.default)` and is reported as single-caller coverage; there is no parallel
fixed-caller family. `certifiedAt_default` and `translation_of_compiled` carry the existing
single-frame results (`Shapes.Certified`, `Shapes.Compiled`) into the default context.

## Tiers

* **Unconditional / conditional.** `spec.assumptions = []` is the unconditional tier. Any named
  assumption makes the statement conditional; each is a hypothesis of the statement, never folded
  into a global premise. Per-call premises (a scoped Keccak-256 separation) belong in
  `spec.Valid` at the call, and `Spec.Covered` makes them satisfiable in the covered context.
* **Runtime / lifecycle.** `Expected` is the runtime tier: every valid call from any storage the
  spec admits. It does not state that the constructor establishes the invariant a
  specification's precondition assumes, that every entrypoint preserves it, or anything about
  reentrant calls. A lifecycle certificate is a separate tier and is not provided
  (`lifecycle`: BLOCKED in docs/SUPPORTED_ENVELOPE.md).

## Resources and out-of-gas

`ResourcesAt` is observable equality from the bound on. `Final.Target.runMsg` keeps only
`evm.error.isNone`, so an empty revert and an out-of-gas halt have the same observable: where the
source reverts with empty data, the bound does not by itself exclude out-of-gas. Reports say
"from the bound on the bytes give the source's observable", never "does not run out of gas", and
never claim the bytes fail below the bound. A reason-aware judgment (keeping EthLib's error kind)
needs a change to `Verify/Final.lean` and the assembly checkers' gas theorems; it is listed as a
gap below.

## The certificate a proof supplies

```lean
-- Verify/Generic/Certificate.lean
structure Certificate (src : Source) (spec : Spec) (bytes : List Nat) where
  code : ByteArray
  bound : code.data.toList.map (·.toNat) = bytes          -- fresh export = fresh compile (decide +kernel)
  checked : ∃ c, src.checked = .ok c                       -- contract_ok
  translation : spec.Assumed → ∀ ctx, spec.Contexts ctx → ∀ c, src.checked = .ok c →
    TranslationAt (src.semAt ctx) c ctx code (spec.Valid ctx) (spec.gas ctx)
  specProof : spec.Assumed → ∀ ctx, spec.Contexts ctx → ∀ c, src.checked = .ok c →
    SpecProof (src.semAt ctx) c (spec.Valid ctx) (spec.Allowed ctx) (spec.Post ctx)
  covered : spec.Covered

theorem Certificate.expected : Certificate src spec bytes → Expected src spec bytes
```

Existing pieces it composes (reused, not rebuilt):

| Field | From |
|---|---|
| `translation` | (Verify/Generic/Compose.lean) `Shapes.compiled_of` (Verify/ShapeGeneric.lean: generic source stage, solar-tv's backend stages, the loop checker), `compiled0XL` (checker with contexts and gas), via `translation_of_compiled`; `TranslationAt.restrict` is the scope check (a stage on a scope covering `Valid`) |
| `specProof` | `specProof_of_holds` (solar-verify's exported spec: `Shapes.allowed_of_holds`, `meets_of_bundle`); `meets_of_discharged` (Verify/Generic/VC.lean: per function, `Verify.VC.triple_of_discharged` in Verify/VC/EndToEnd.lean, i.e. Verify/Discharge's `dischargeScript`, `checkScript` and `Binds`); or a reviewed Lean proof |
| `covered` | per-entry valid calls and the non-vacuity witnesses each spec module already proves |

Loops are not special in the statement. A loop's termination within the fuel and the stage
through it are part of `translation`, proved from a supplied, kernel-checked invariant and ranking
certificate; a contract with a loop and no certificate is BLOCKED before any proof is attempted.
No claim of automatic verification: invariants and lemmas may have to be supplied.

## The driver's statement module (T1)

The statement module is the same template for every contract:

```lean
import Verify.Generic.Expected
import <the fresh solc-AST source module>
import <the reviewed spec module>
namespace Certified.<name>.Final
def runtimeBytes : List Nat := [<bytes from this run's compile>]
def Statement : Prop := SolidCore.Verify.Generic.Expected <src> <spec> runtimeBytes
end Certified.<name>.Final
```

and the final module states `theorem final : Statement := <proof module's certificate>.expected`.
The checker requires `final`'s type to be exactly `Statement`, `Statement` not to import the proof
module, `final`'s axioms to be among `propext`, `Classical.choice`, `Quot.sound`, and (hypothesis
audit) `final` to take no arguments: every assumption is in `spec.assumptions`, which the report
lists, and the tier is unconditional only when that list is empty.

Before the proof, the driver runs the envelope gate
(`Verify/Generic/envelope_check.py`, docs/SUPPORTED_ENVELOPE.md) on the fresh solc AST with the
declared entries and supplied loop certificates, and emits BLOCKED with its reasons when it says
so. A contract the gate passes is Certified only when the kernel checks `Expected`.

## Instances (acceptance)

| Contract | Module | Coverage | Tier |
|---|---|---|---|
| Counter (`inc`, `get`) | `Verify/Generic/Instances/Counter.lean`, lib `VerifyGeneric` | default context; entries `inc`, `get` | unconditional, runtime |
| UniswapV2ERC20.transfer | `Verify/Generic/Instances/Transfer.lean`, lib `VerifyGenericTransfer` (needs the generated port; lands after its build) | default context; entry `transfer(address,uint256)`; scoped Keccak-256 separation in `Valid` | unconditional with a per-call premise, runtime |

Both are proved from the existing theorems (`Contracts.Counter.ShapeExport.published`,
`SolidCore.Spec.UniswapV2.ERC20.Certified.certified`) through `certifiedAt_default`; neither adds
a contract-specific statement.

## Shape selection to remove from acceptance

These choose the published statement per contract and must route through `Expected` instead
(outside this interface's files; for the driver and integration owners):

* solar `tools/certify/final.py`: `shape.json` `kind` selects among `Shapes.Certified`,
  `Shapes.Functional`, `Shapes.OpenFunctional` and `Shapes.Compiled`, with free-form Lean terms for
  `valid`, `allowed`, `post`, `gas`. Only `Expected` is reported Certified; the other kinds become
  "not certified" statuses with their reason.
* solidity-lean `Certified/*/Final.lean` and `record.json`: generated per contract from those
  kinds; regenerate from the template above.
* solidity-lean `scripts/refinement/axiom-audit.sh`: a fixed list of audited parts; the generic
  check is the closed-type and axiom check of `final` above.

## Known gaps

* Reason-aware gas (out-of-gas vs empty revert): not stated (see above).
* Only the caller is a context parameter; the contract's address, block and transaction are fixed.
* Lifecycle tier (constructor establishment, preservation by every entrypoint, reentrancy): not
  provided.
* The existing instances cover one context; any-caller results (`ResourcesFrom`) exist for
  transfer's translation only, not for its specification.
