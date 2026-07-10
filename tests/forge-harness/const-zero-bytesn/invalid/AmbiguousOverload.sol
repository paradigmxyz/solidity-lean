// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Mirror over-accept guard: with both g(uint256) and g(bytes32), the folded 0
// argument `1 - 1` matches BOTH candidates -> no unique declaration. solc
// rejects ("No unique declaration found after argument-dependent lookup"); the
// model must too.
contract AmbiguousOverload {
    function g(uint256) public pure returns (uint256) {
        return 1;
    }

    function g(bytes32) public pure returns (uint256) {
        return 2;
    }

    function h() external pure returns (uint256) {
        return g(1 - 1);
    }
}
