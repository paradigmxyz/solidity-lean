# Inheritance & Virtual/Override Dispatch Review vs solc 0.8.35

Scope: which function body actually runs under inheritance (dispatch), plus the
accept/reject rules around `virtual`/`override`/abstract. Ground truth: pinned
solc 0.8.35 (`--standard-json`, legacy pipeline) + observed behaviour through
solidity-lean's solc-AST importer and `SolidCore.Solidity.TypeCheck` /
`Checked` interpreter. Search-only; no semantics were modified.

Method: each candidate was compiled with pinned solc for the accept/reject
verdict, imported into Lean via `scripts/solc_ast_to_lean_source.py`, and where a
value was observable it was executed with
`TypeCheck.Examples.checkedCallWordMatches` / `CheckedInput.callContract`. For
programs solc rejects at analysis time (no AST is emitted), lean's independent
verdict was obtained by mutating the Lean AST generated from the accepted
sibling program (e.g. stripping an `override(B,C)` base list to a bare
`override`) and re-running `importedContractAccepted`.

## Summary

| # | Feature | Verdict |
|---|---------|---------|
| 1 | Most-derived override via internal `f()` / base-method dynamic dispatch | CLEAN |
| 1 | `this.f()` external self-dispatch | INCONCLUSIVE (harness can't run external self-call) |
| 2 | `super.f()` C3 MRO in a diamond | CLEAN |
| 3 | Explicit base qualification `Base.f()` | **DIVERGENCE — over-reject (90%)** |
| 4 | `override(A,B)` multi-base specifier accept/reject | CLEAN |
| 5 | `virtual` requirement / missing-`override` reject | CLEAN |
| 6 | Abstract instantiation reject | CLEAN |
| 7 | Public state-variable getter overriding a virtual external fn | CLEAN |
| 9 | Function overloading × inheritance | CLEAN |
| 10 | Modifier virtual/override dispatch | CLEAN |

One real divergence found (#3). Priority items #2, #4, #6 are all clean with
evidence.

---

## DIVERGENCE #3 — Explicit base-qualified call `Base.f()` is over-rejected

**Confidence: 90%. Severity: over-reject (valid contract rejected at typecheck).**

### Program
```solidity
pragma solidity 0.8.35;
contract A { function f() public virtual returns (uint) { return 1; } }
contract B is A {
  function f() public override returns (uint) { return 2; }
  function viaBase() public returns (uint) { return A.f(); }   // static call to A's body
}
```

### solc 0.8.35
ACCEPTS. `A.f()` is a legal statically-bound call to base `A`'s implementation;
`B().viaBase()` returns `1` (A's body), bypassing B's override.

### solidity-lean
REJECTS the whole contract. `importedContractAccepted = false`; the call
`viaBase` fails typechecking with:
```
Except.error (TypeError.unsupported "member call f")
```
This reproduces for a plain linear base (`B is A`), not only diamonds.

### Root cause
The base-qualified-call rewrite is keyed on the wrong AST shape. In
`SolidCore/Solidity/Interface.lean:496` (`Expr.rewriteBaseCallsFuel`):
```lean
| Expr.call (Expr.member (Expr.ident baseName) member) args =>
    if nameIn baseName baseNames then
      Expr.call (Expr.ident (baseHelperName baseName member)) ...
```
It matches only when the qualifier is `Expr.ident baseName`. But the solc
importer renders a base **contract name** as a *type* node, not an identifier:
`A.f()` becomes
`Expr.member (Expr.typeName (Ty.user {segments := ["A"]})) "f"`
(verified in the generated AST). The `Expr.ident` arm therefore never fires for
real solc ASTs, the expression falls through to the generic call arm
(`Interface.lean:503`) unchanged, and the type-checker's `typeName`-member-call
handler rejects a call on a non-library contract type at
`SolidCore/Solidity/TypeCheck.lean:6186-6189`:
```lean
else
  Except.error (TypeError.unsupported ("member call " ++ member))   -- 6186
| none =>
  Except.error (TypeError.unsupported ("member call " ++ member))   -- 6188
```
(The branch there only handles user-value-type `wrap`/`unwrap` and *library*
calls; a base *contract* qualifier is unhandled.)

Contrast with `super.f()`, which works: `super` is a keyword and the importer
emits it as `Expr.member (Expr.ident "super") "f"` (verified), so the
`super` rewrite at `Interface.lean:348` *does* match. The whole
`__base_<Base>_<fn>` helper machinery
(`Interface.lean:328-329, 496-502, 642-655`; TypeCheck
`checkExplicitBaseMemberCallArgsContextual` at `TypeCheck.lean:7672-7689`) is
effectively unreachable from solc-imported programs because of the
`Expr.ident` vs `Expr.typeName` mismatch. Any hand-written witness that spells
the base as `Expr.ident "A"` would exercise it and pass, masking the gap.

### Fix sites (not applied — search only)
Either (a) `scripts/solc_ast_to_lean_source.py` should render a base-contract
member-access qualifier as `Expr.ident <name>` rather than `Expr.typeName`, or
(b) `Interface.lean:496` + `TypeCheck.lean` should also match
`Expr.member (Expr.typeName (Ty.user path)) member` where `path` resolves to a
base contract and route it to the base-helper / explicit-base-call path.

### Confidence note (why 90% not higher)
solc's ACCEPT and the returned value are certain. The 10% reservation is only
about attribution boundary (importer rendering vs. core rewrite): the end-to-end
pipeline unambiguously over-rejects a valid program, but a maintainer may class
the fix as "importer" rather than "semantics". The observable divergence stands
regardless.

---

## Clean negatives (with evidence)

**#1 Most-derived override / dynamic dispatch — CLEAN.**
`contract Der is Base` overriding `f`; `Base.callF()` does internal `f()`.
`Der().callF()` returns `2` (the derived override — the base method sees the
most-derived body). `Except.ok true`.

**#1 `this.f()` — INCONCLUSIVE.** External self-call requires a scripted-responder
environment that `checkedCallWordMatches` does not set up (fails with
`unsupported "checked executable contract call Der"`, `Checked.lean:18`). The
contract type-checks (`importedContractAccepted = true`); dispatch could not be
observed. Not counted as a divergence. The runtime function table is the same
deduped most-derived table used by internal calls, so correct behaviour is
likely, just not exercised here.

**#2 `super.f()` in a diamond — CLEAN (priority).**
```solidity
contract A { function f() public virtual returns (uint){return 1;} }
contract B is A { function f() public virtual override returns(uint){return super.f()+10;} }
contract C is A { function f() public virtual override returns(uint){return super.f()+100;} }
contract D is B,C { function f() public override(B,C) returns(uint){return super.f()+1000;} }
```
C3 linearization of D is `D, C, B, A`, so the super chain is D→C→B→A and
`A.f` runs exactly once. Expected `D.f() = 1111`. solidity-lean returns
`1111` (`Except.ok true`). Matches. Super resolution steps the C3 MRO, not the
direct parent (`Interface.lean` `contextualSuperHelpersFor?` uses
`afterName? dispatchOrder`).

**#4 `override(A,B)` multi-base specifier — CLEAN (priority).**
- Correct `override(B,C)` diamond: solc ACCEPT, lean ACCEPT.
- Bare `override` in the diamond: solc REJECTS ("Function needs to specify
  overridden contracts B and C"). Testing lean independently by stripping the
  `override(B,C)` base list to `some { bases := [] }` in the generated AST →
  `importedContractAccepted = false`. No over-accept.
  (`checkOverrideSpecifier`, `TypeCheck.lean:10049-10064`.)

**#5 `virtual`/`override` keyword rules — CLEAN.**
- Override of a **non-virtual** base function (mutate base `virtual := false`,
  keep derived `override`): lean rejects (`false`). solc rejects too.
- **Missing `override`** while shadowing a virtual base (mutate derived
  `override? := none`): lean rejects (`false`). solc rejects too.
  (`checkOverridable` / `checkOverrideUse`, `TypeCheck.lean:9820-9825`,
  `10066-10074`.)

**#6 Abstract instantiation — CLEAN (priority).**
- `new Abs()` where `Abs` is abstract (mutate an accepted `new Impl()` AST's
  created type to `Abs`): lean rejects (`false`). solc rejects. Root check
  `requireCreatableContractDecl`, `TypeCheck.lean:4822-4829`.
- Concrete contract that declares/inherits an unimplemented function (mutate
  `Impl.f` body to `none`): lean rejects (`false`). solc rejects ("should be
  marked abstract"). Check `checkInheritedAbstractImplementedAux`,
  `TypeCheck.lean:10183-10205`.
- Abstract used as a base, dynamic dispatch through it: abstract `Abs.g()` calls
  unimplemented `f()`; `Impl` (concrete) overrides `f`→3; `Impl.g()` returns
  `8`. `Except.ok true`. Correct.

**#7 State-variable getter overriding a virtual external fn — CLEAN.**
```solidity
abstract contract Base { function value() external view virtual returns (uint); }
contract C is Base { uint public override value; function setIt() public { value = 42; } }
```
solc ACCEPT, lean ACCEPT. After `setIt()`, calling `value()` dispatches to the
synthesized getter and returns `42` (`Except.ok true`).
(`StateVarDecl.publicGetterOverrideMember?`, `TypeCheck.lean:9876-9896`.)

**#9 Overloading × inheritance — CLEAN.**
```solidity
contract A { function f(uint x) public virtual returns (uint){return x+1;} }
contract B is A {
  function f(uint x, uint y) public returns (uint){return x+y;}
  function f(uint x) public override returns (uint){return x+100;}
}
```
`B.f(5) = 105` (overload resolves to 1-arg signature, then the derived
override), `B.f(5,6) = 11`. Both `Except.ok true`.

**#10 Modifier virtual/override — CLEAN.**
```solidity
contract A { uint public tag; modifier m() virtual { tag=1; _; } function f() public m returns(uint){return tag;} }
contract B is A { modifier m() override { tag=2; _; } }
```
`B.f()` runs B's overridden modifier → returns `2`; `A.f()` runs A's → `1`.
Both `Except.ok true`. Most-derived modifier override is dispatched.

**#8 Constructor dispatch order** — not separately re-tested; covered by the
prior DL1 storage/constructor-order work (reverse-C3). No new dispatch bug
surfaced while exercising the diamond above.

---

## Harness limitations noted
- Programs solc rejects at analysis time emit no AST, so lean's independent
  accept/reject can only be probed by mutating the accepted sibling's generated
  AST (done for #4/#5/#6). Direct import of a solc-rejected `.sol` fails at the
  importer, not in lean.
- External self-calls (`this.f()`) require a scripted responder; the plain
  `checkedCallWordMatches` path cannot execute them.
