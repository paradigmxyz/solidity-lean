// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ModifierOverload {
    modifier guarded(uint256 value) {
        _;
    }

    modifier guarded(address target) {
        _;
    }
}
