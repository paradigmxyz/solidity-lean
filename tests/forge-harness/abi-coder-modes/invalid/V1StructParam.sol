// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma abicoder v1;

contract V1StructParam {
    struct S {
        uint256 value;
    }

    function use(S memory input) external pure returns (uint256) {
        return input.value;
    }
}
