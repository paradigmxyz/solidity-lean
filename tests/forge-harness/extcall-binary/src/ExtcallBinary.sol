// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// EXTCALL-BINARY (call-position Cluster B #7) — an EXTERNAL/member single-return
// call nested inside a BINARY operand. The Executable core represents user calls
// as STATEMENTS, so a call nested in a larger expression must be hoisted into a
// prefix statement binding a temp. The recursive binary/condition hoister only
// recognised INTERNAL ident calls, so any EXTERNAL/member call inside a binary
// (`require(t.balanceOf(a) >= amt)`, `uint y = t.n() + 1`, `while (i < t.limit())`,
// `if (t.ok() && cond)`, `return t.n() + g`, `x = t.n() + 1`) over-rejected even
// though solc accepts every one. The fix extends the SAME hoisting seam: when an
// operand is a single external member call and the other operand is pure, the
// call is lowered via the existing `tryExternalCall` machinery in its source
// position (solc legacy left-to-right order), the result bound to a temp, and the
// operand replaced by the temp. `&&`/`||` with the call on the RIGHT materialise
// the short-circuit as an `ifElse` on the pure-lhs temp so the effectful external
// call is skipped exactly when solc skips it.
//
// The calls here are EXTERNAL self-calls (`this.f(..)`, becoming STATICCALLs), so
// acceptance (lowering) is pinned by importedContractAccepted; the Forge test
// exercises real solc/EVM execution against the deployed contract. The contract
// is self-contained so no user-typed state var blocks import.
contract ExtcallBinaryHarnessTarget {
    uint256 private stored = 3;

    // Public single-return helpers used as external self-calls in binary operands.
    function n() public view returns (uint256) {
        return stored; // 3
    }

    function limit() public pure returns (uint256) {
        return 5;
    }

    function ok() public pure returns (bool) {
        return true;
    }

    function balanceOf(address a) public pure returns (uint256) {
        a; // silence unused
        return 100;
    }

    // #7a require(...) guard: external call on the LEFT of `>=`, pure on the RIGHT
    // (THE canonical ERC20 balance-guard idiom). Reverts when amt > 100.
    function requireGuard(address a, uint256 amt) external view returns (uint256) {
        require(this.balanceOf(a) >= amt, "insufficient");
        return amt;
    }

    // #7b var-decl init with an external call in a `+` binary (call on the LEFT).
    function varDeclInit() external view returns (uint256) {
        uint256 y = this.n() + 1; // 3 + 1 = 4
        return y;
    }

    // #7c assignment RHS binary with an external call (call on the LEFT).
    function assignRhs() external view returns (uint256) {
        uint256 x = 0;
        x = this.n() + 1; // 4
        return x;
    }

    // #7d while loop-condition with an external call in a `<` binary (call on the
    // RIGHT — exercises the pure-lhs-into-temp path, re-evaluated each iteration).
    function whileCond() external view returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;
        while (i < this.limit()) {
            acc += i;
            i += 1;
        }
        return acc; // 0 + 1 + 2 + 3 + 4 = 10
    }

    // #7e if-condition with an external call in an `&&` binary (call on the LEFT).
    function ifAnd(bool cond) external view returns (uint256) {
        if (this.ok() && cond) {
            return 1;
        }
        return 0;
    }

    // #7f if-condition with an external call on the RIGHT of `||` (exercises the
    // short-circuit `ifElse` branch: the call is skipped when cond is true).
    function ifOr(bool cond) external view returns (uint256) {
        if (cond || this.ok()) {
            return 1;
        }
        return 0;
    }

    // #7g return with an external call in a `+` binary (call on the LEFT).
    function returnBin(uint256 g) external view returns (uint256) {
        return this.n() + g; // 3 + g
    }
}
