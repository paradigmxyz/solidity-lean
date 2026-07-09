# solc contract-creation review (Fable adversarial, 0.8.35 LEGACY)

Scope: observable semantics of `new C(...)`, `new C{salt:…}(...)`, `new C{value:…}(...)`,
and `try new C…`. Out of scope (intentional exclusion): create-initCode-as-real-bytecode,
`creationCode`/`runtimeCode` byte content, closed-world constructor-body execution.

Evidence base: solc source `libsolidity/codegen/ExpressionCompiler.cpp` (Creation /
FunctionCallOptions paths) + `libsolidity/analysis/TypeChecker.cpp`, cross-checked against
the pinned binary `/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35` (legacy
`--asm` source-map ordering). solidity-lean traced in `Interpreter.lean` / `Interface.lean` /
`TypeCheck.lean`.

---

## solc reference behavior (established, asm-verified)

`ExpressionCompiler::visit(FunctionCall)` Creation case (line 750):
1. `_functionCall.expression().accept(*this)` runs FIRST — for a `{…}` creation this is the
   `FunctionCallOptions` node, whose `visit` (line 1574) evaluates the options **in source
   order** (`options()[i]`, `i = 0..n`).
2. THEN the constructor arguments are evaluated (loop at line 758).

So solc order is: **options in source order → constructor args LAST**. Asm-confirmed:
- `new T{salt: tickSalt(), value: tickVal()}(tickArg())` → `tickSalt, tickVal, tickArg`.
- `new T{value: tickVal(), salt: tickSalt()}(tickArg())` → `tickVal, tickSalt, tickArg`.
- `try new T{value: tickVal(), salt: tickSalt()}(tickArg())` → `tickVal, tickSalt, tickArg`.

---

## CONFIRMED DIVERGENCE 1 — try-create evaluates args BEFORE options (args-first)

**Classification:** wrong-evaluation-order. **Confidence:** high.

**Repro**
```solidity
contract Target { constructor(uint256 a) payable {} }
contract F {
    uint256 public seq; uint256 public argSeq; uint256 public valSeq; uint256 public saltSeq;
    function tickArg() internal returns (uint256){ seq++; argSeq = seq; return 0; }
    function tickVal() internal returns (uint256){ seq++; valSeq = seq; return 1; }
    function tickSalt() internal returns (bytes32){ seq++; saltSeq = seq; return bytes32(0); }
    function go() external payable {
        try new Target{value: tickVal(), salt: tickSalt()}(tickArg()) returns (Target) {} catch {}
    }
}
```

**solc:** `tickVal → tickSalt → tickArg` (args LAST). Asm source-map lines 140/147/156.
Post-state: `valSeq=1, saltSeq=2, argSeq=3`.

**solidity-lean:** `Interpreter.lean:8736-8754` — the `Stmt.tryContractCreate` handler
evaluates the three top-level sub-expressions by explicit Lean sequencing:
`constructorArgsExpr` (8738) → `valueExpr` (8742) → `saltExpr` (8751). Args are forced
FIRST, then value, then salt, regardless of `ChildEvalOrder`. Post-state:
`argSeq=1, valSeq=2, saltSeq=3`.

**Divergence:** args-vs-options ordering is completely inverted (solc args-last; lean
args-first). Observable whenever a constructor arg AND a value/salt option carry
side effects. Note this handler also disagrees with the interpreter's *own* plain-create
handler (see below), which is right-to-left.

---

## CONFIRMED DIVERGENCE 2 — plain-create ignores source order of value vs salt

**Classification:** wrong-evaluation-order. **Confidence:** high. **Severity:** lower than #1.

**Repro:** as above but `new Target{value: tickVal(), salt: tickSalt()}(tickArg());`
(no `try`).

**solc:** options in source order → `tickVal → tickSalt → tickArg`. Asm lines 140/147/156
of `Order2.sol`. (`{salt:…, value:…}` gives `tickSalt → tickVal → tickArg`.)

**solidity-lean:** the surface loses option source order at lowering. `Interface.lean:4806`
`CallOptions.contractCreationValueSaltCore?` maps both `[value, salt]` and `[salt, value]`
to the same `(some valueCore, some saltCore)`. The plain-create handler
(`Interpreter.lean:6586-6595`) builds the fixed list `[constructorArgsExpr, valueExpr,
saltExpr]` and evaluates it with the pinned `ChildEvalOrder.rightToLeft`
(`Interpreter.lean:7099`, resolved at 7102) → **salt → value → args**, always.

**Divergence:** for `{salt:…, value:…}` source order lean matches solc (both salt→value→args).
For `{value:…, salt:…}` source order solc evaluates value→salt→args but lean still evaluates
salt→value→args — value/salt swapped. Observable when both options carry side effects and
are written value-before-salt.

---

## Clean negatives (verified, NO divergence)

- **`{value:}` on a non-payable constructor — correctly REJECTED.** solc errors
  (TypeChecker.cpp:2985, "Cannot set option \"value\", since the constructor … is not
  payable"; binary-confirmed). solidity-lean rejects via `requireValueOptionAllowed`
  (`TypeCheck.lean:4234`, called at `TypeCheck.lean:6626`). Not an over-accept.
- **`new` on abstract / interface / library — correctly REJECTED.**
  `requireCreatableContractDecl` (`TypeCheck.lean:4746-4753`, called at 6557/6926) requires
  `kind == contract` and `!abstract`. Matches solc.
- **`{salt:}` gating.** solidity-lean requires Constantinople-or-later for salt
  (`TypeCheck.lean:6547`); consistent with solc's create2 availability.
- **Constructor args evaluated LAST relative to options in the plain path** — matches solc
  (rightToLeft over `[args, value, salt]` puts args last). Only the try path (#1) is wrong here.
- **Failed-creation revert bubbling.** solc `appendConditionalRevert(true)` (ExpressionCompiler
  line 810) bubbles constructor returndata on a non-try failed CREATE. solidity-lean throws
  `SolidityFailure.revert (RevertData.fromRawBytes result.output)` (`Interpreter.lean:6613/6631`)
  — bubbles the create output. Consistent.
- **`{value:}` ETH transfer / balance-insufficient revert / freshly-created-code extcodesize /
  msg.sender==creator inside the constructor body.** These are resolved on the open-world
  external boundary (`emitContractCreation`, `Interpreter.lean:2424`) and answered by the
  scripted responder / differential, not independently modeled — the intentional
  closed-world creation exclusion, not a divergence.

---

## Summary

Two confirmed wrong-evaluation-order divergences, both in the sub-expression evaluation
ordering of contract creation, both observable only via side-effecting option/arg
expressions:
1. **try-create is args-first** (solc is args-last / options-first) — broader, and also
   internally inconsistent with the plain-create handler.
2. **plain-create fixes salt-before-value**, ignoring source order (diverges on
   `{value:…, salt:…}`).

All type-level accept/reject surfaces in scope (payable-ctor value gating, abstract/
interface/library rejection, salt gating) are correct. Value-transfer/balance/revert-bubble
observables are the intentional open-world boundary.
