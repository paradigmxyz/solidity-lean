// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface I {}

contract InterfaceCreationCode {
    function bad() external pure returns (bytes memory) {
        return type(I).creationCode;
    }
}
