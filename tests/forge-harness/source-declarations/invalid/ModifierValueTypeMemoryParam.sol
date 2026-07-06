// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ModifierValueTypeMemoryParam {
    modifier withValue(uint256 memory value) {
        _;
    }
}
