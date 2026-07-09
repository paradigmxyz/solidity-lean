// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Exercises constructor ARGUMENTS: both engines deploy with the same decoded
// args (EVM appends them to creationCode; solidity-lean passes them to
// constructWithContext). No observed_slots declared — broad storage compares
// slot0 automatically.
contract CtorArgs {
    uint256 public v;          // slot 0

    constructor(uint256 x) {
        v = x * 2;
    }

    function get() external view returns (uint256) {
        return v;
    }
}
