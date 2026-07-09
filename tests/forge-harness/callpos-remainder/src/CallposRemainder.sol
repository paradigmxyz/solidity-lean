// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CALLPOS-REMAINDER — the two highest-reachability remaining over-rejects in the
// call-position family (a user CALL is a STATEMENT in the Executable core, so a
// call nested in a sub-expression must be HOISTED into a prefix temp-binding):
//
//   Bug 1: the compound-assign RHS contains a user call — `total += fee()`,
//          `m[k] += f()`, `x += this.g()`. The compound-op statement arm routed
//          every compound-assign through the env-aware pure lowering, which
//          returns `none` for any call RHS, so solidity-lean over-rejected the
//          whole function. The fix hoists the call into a prefix statement and
//          feeds the (pure temp-read) result as the RHS of the SAME
//          `assignOpCleanupExpr` node, so the LValue-width COMPOUND-CLEANUP
//          (Panic 0x11 on narrow `+=`, truncating `<<=`) is preserved. solc
//          evaluates the RHS call FIRST (verified via `--ir`: for `x += f()`
//          and `m[k] += f()` the call is emitted BEFORE the LValue read/index),
//          which the prefix-then-cleanup shape reproduces exactly.
//
//   Bug 2: a DIRECT storage array `.push(<call>)` whose argument is a user call
//          — `xs.push(f())`, `xs.push(this.g())`. The pure push path cannot
//          lower a call argument. The fix hoists the call into a prefix
//          statement, then pushes the temp-read through the existing
//          `storageArrayPushRef` path (restricted to receivers that read no
//          dynamic index, matching solc's evaluate-arg-then-push order).
//
// The Bug-1 INTERNAL-call variants live in `CallposRemainderHarnessTarget` (the
// solc_import `--contract`, so `importedContract`), which is fully executable-
// lowerable; own-contract execution pins their acceptance AND semantics —
// including two eval-order pins (`orderInternal`, `mapOrderInternal`) whose
// result is only correct if the call runs BEFORE the LValue, and the narrow-
// width Panic 0x11 / `<<=`-truncation controls proving the compound-cleanup
// survives the hoist. Bug 2 (`push`) and the Bug-1 EXTERNAL (`this.`-self-call)
// variants live in `CallposRemainderExtPush`: solidity-lean's own-call executor
// has no dynamic-array/external-self-call support, so these are pinned by
// `importedContractAccepted` (whole-source-unit acceptance = the fix's lowering)
// and exercised against real solc/EVM by the Forge test. Call-free controls
// (`plainCompoundControl`, `plainPushControl`) pin the pre-existing paths.
contract CallposRemainderHarnessTarget {
    mapping(uint256 => uint256) private mm;
    uint256 private kk;
    uint8 private nb;

    // Internal single-return helpers (own-call executable).
    function fee() internal pure returns (uint256) {
        return 37;
    }

    function fee8() internal pure returns (uint8) {
        return 55;
    }

    function fee8big() internal pure returns (uint8) {
        return 100;
    }

    function shiftBy() internal pure returns (uint8) {
        return 4;
    }

    // Internal helper that MUTATES the state var shared with the LValue, so the
    // result distinguishes call-before-read from read-before-call.
    function bump() internal returns (uint256) {
        kk = 100;
        return 1;
    }

    // Internal helper that MUTATES the mapping index variable `kk`.
    function setK() internal returns (uint256) {
        kk = 1;
        return 10;
    }

    // Bug 1 — internal call in a `+=` RHS on a plain state var. 5 + 37 = 42.
    function addInternal() external returns (uint256) {
        kk = 5;
        kk += fee();
        return kk;
    }

    // Bug 1 — eval-order pin. solc evaluates `bump()` FIRST (sets kk = 100,
    // returns 1), THEN reads kk (= 100), so 100 + 1 = 101. A read-before-call
    // order would give 5 + 1 = 6.
    function orderInternal() external returns (uint256) {
        kk = 5;
        kk += bump();
        return kk;
    }

    // Bug 1 — internal call in a `+=` RHS on a mapping LValue. 5 + 37 = 42.
    function mapAddInternal() external returns (uint256) {
        mm[3] = 5;
        mm[3] += fee();
        return mm[3];
    }

    // Bug 1 — mapping-LValue eval-order pin. solc evaluates `setK()` FIRST
    // (kk = 1, returns 10), THEN reads the index kk (= 1), so mm[1] += 10 gives
    // 7 + 10 = 17. A read-before-call order would target mm[0] and leave
    // mm[1] == 7.
    function mapOrderInternal() external returns (uint256) {
        kk = 0;
        mm[0] = 5;
        mm[1] = 7;
        mm[kk] += setK();
        return mm[1];
    }

    // Bug 1 — narrow (uint8) `+=` with a call RHS, IN RANGE. 100 + 55 = 155.
    function narrowInRange() external returns (uint8) {
        nb = 100;
        nb += fee8();
        return nb;
    }

    // Bug 1 — narrow (uint8) `+=` with a call RHS, OVERFLOWS: 200 + 100 = 300 >
    // 255 -> Panic 0x11. Proves the LValue-width COMPOUND-CLEANUP is preserved
    // through the call hoist (checked cleanup still fires).
    function narrowOverflow() external returns (uint8) {
        nb = 200;
        nb += fee8big();
        return nb;
    }

    // Bug 1 — narrow (uint8) `<<=` with a call RHS. `16 << 4 == 256` truncates
    // to uint8 == 0 (no overflow check on `<<=`, even checked). Proves the
    // truncating cleanup is preserved through the call hoist.
    function narrowShlCall() external returns (uint8) {
        nb = 16;
        nb <<= shiftBy();
        return nb;
    }

    // Bug 1 — control: call-free compound-assign must be unchanged. 10 + 5 = 15.
    function plainCompoundControl() external returns (uint256) {
        kk = 10;
        kk += 5;
        return kk;
    }
}

// Bug 2 (`push`) and Bug-1 EXTERNAL (`this.`-self-call) repros. Acceptance is
// pinned by `importedContractAccepted` (whole-source-unit checkedSourceUnit, so
// these must LOWER); runtime is exercised by the Forge test against real EVM.
contract CallposRemainderExtPush {
    uint256[] private xs;
    uint256 private kk;

    function fee() internal pure returns (uint256) {
        return 37;
    }

    // Public helper used as a bare external self-call (`this.g()`).
    function g() public pure returns (uint256) {
        return 37;
    }

    // Bug 2 — storage array `.push(<internal call>)`. Pushes 37, returns xs[0].
    function pushInternal() external returns (uint256) {
        xs.push(fee());
        return xs[0];
    }

    // Bug 2 — control: call-free push must be unchanged. Pushes 9, returns xs[0].
    function plainPushControl() external returns (uint256) {
        xs.push(9);
        return xs[0];
    }

    // Bug 2 — storage array `.push(this.g())` (external). Pushes 37, returns
    // xs[0].
    function pushExternal() external returns (uint256) {
        xs.push(this.g());
        return xs[0];
    }

    // Bug 1 — external `this.g()` in a `+=` RHS. 5 + 37 = 42.
    function addExternal() external returns (uint256) {
        kk = 5;
        kk += this.g();
        return kk;
    }
}
