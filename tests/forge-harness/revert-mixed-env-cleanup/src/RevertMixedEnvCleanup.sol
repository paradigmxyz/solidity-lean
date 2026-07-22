// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract RevertMixedEnvCleanupHarnessTarget {
    error Err(uint8 s, uint256 k);

    uint256 private c;

    function bump() internal returns (uint256) {
        c += 1;
        return c;
    }

    function run(uint8 a, uint8 b) external {
        revert Err(a + b, bump());
    }
}
