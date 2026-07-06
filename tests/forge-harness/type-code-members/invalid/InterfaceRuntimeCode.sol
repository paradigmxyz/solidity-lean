// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface I {}

contract InterfaceRuntimeCode {
    function bad() external pure returns (bytes memory) {
        return type(I).runtimeCode;
    }
}
