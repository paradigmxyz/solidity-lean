// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma abicoder v1;

contract V1AbiEncodeStruct {
    struct S {
        uint256 value;
    }

    function encode() external pure returns (bytes memory) {
        return abi.encode(S({value: 1}));
    }
}
