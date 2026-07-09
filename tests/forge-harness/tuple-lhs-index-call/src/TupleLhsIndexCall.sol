// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// TUP-IDX — a tuple ASSIGNMENT whose LHS component is indexed by an INTERNAL
// function call: `(xs[f()], z) = (3, 4)`, `(m[k()], z) = (8, 9)`. solc accepts
// and runs these (ordinary Solidity); the index call runs once. solidity-lean
// formerly over-rejected at Executable lowering because the tuple-LHS lvalue
// lowering (`toCoreLValueTargets?` / `toCoreLValue?`) lowered the index with
// the pure `Expr.toCore?`, which has no internal-call case — the explicitly-
// out-of-scope sibling of the MI1 single-assign fix. The fix hoists each
// call-valued LHS index into a per-component temp (reusing the MI1 machinery)
// and builds the tuple target from the temp.
//
// Evaluation order (pinned on Forge): solc evaluates the RHS components
// left-to-right FIRST, then the LHS index expressions left-to-right. `runOrder`
// records that as logv == 3412: `rhs(3)`, `rhs(4)` (RHS), then `tick(1)`,
// `tick1(2)` (LHS indices). An index-first order would give a different digit
// string. Each external entry point starts from a clean state (logv == 0).
contract TupleLhsIndexCallHarnessTarget {
    uint256[3] xs;
    uint256[3] ys;
    mapping(uint256 => uint256) m;
    uint256 public logv;
    uint256 public z;

    // Side-effecting index/key producers: each appends a digit to logv and
    // returns the index/key to use.
    function tick(uint256 v) internal returns (uint256) { logv = logv * 10 + v; return 0; }
    function tick1(uint256 v) internal returns (uint256) { logv = logv * 10 + v; return 1; }
    function keyf() internal returns (uint256) { logv = logv * 10 + 7; return 2; }
    function rhs(uint256 v) internal returns (uint256) { logv = logv * 10 + v; return v; }

    // Array index is an internal call: (xs[tick(1)], z) = (3, 4).
    // tick(1) runs once (logv == 1) and returns index 0, so xs[0] == 3, z == 4.
    function runArray() external returns (uint256) {
        (xs[tick(1)], z) = (3, 4);
        return logv; // 1
    }

    // Mapping key is an internal call: (m[keyf()], z) = (8, 9).
    // keyf() runs once (logv == 7) and returns key 2, so m[2] == 8, z == 9.
    function runMapping() external returns (uint256) {
        (m[keyf()], z) = (8, 9);
        return logv; // 7
    }

    // Two call-valued LHS indices AND call-valued RHS components — the eval
    // order probe. RHS left-to-right (rhs(3), rhs(4)) THEN LHS indices
    // left-to-right (tick(1), tick1(2)) => logv == 3412; xs[0] == 3, ys[1] == 4.
    function runOrder() external returns (uint256) {
        (xs[tick(1)], ys[tick1(2)]) = (rhs(3), rhs(4));
        return logv; // 3412
    }

    // Call in BOTH an LHS index and the RHS: (xs[keyf()], z) = (rhs(3), 9).
    // RHS first (rhs(3): logv->3) then LHS index (keyf(): logv->37); returns
    // key 2, so xs[2] == 3, z == 9.
    function runBoth() external returns (uint256) {
        (xs[keyf()], z) = (rhs(3), 9);
        return logv; // 37
    }

    // Readers (used to confirm the stored values on both sides).
    function getXs(uint256 i) external view returns (uint256) { return xs[i]; }
    function getYs(uint256 i) external view returns (uint256) { return ys[i]; }
    function getM(uint256 k) external view returns (uint256) { return m[k]; }
    function getZ() external view returns (uint256) { return z; }
}
