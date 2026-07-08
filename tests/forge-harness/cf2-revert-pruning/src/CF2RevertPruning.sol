// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CF2: `pick` returns a storage pointer `p`; the only path that leaves the
// named-return obligation unmet runs through `alwaysReverts()`, which never
// returns. solc prunes that edge (ControlFlowRevertPruner) and accepts; this is
// the over-reject the CF2 fix removes. The non-reverting path (c == true)
// binds and returns `xs`, so the value is well defined.
contract CF2RevertPruningHarnessTarget {
    uint256[] private xs;

    function alwaysReverts() internal pure {
        revert("cf2 unreachable");
    }

    function pick(bool c) internal returns (uint256[] storage p) {
        if (c) {
            p = xs;
            return p;
        }
        alwaysReverts();
    }

    function seed() external {
        xs.push(11);
        xs.push(22);
        xs.push(33);
    }

    function pickLength() external returns (uint256) {
        return pick(true).length;
    }

    function pickAt(uint256 i) external returns (uint256) {
        return pick(true)[i];
    }
}
