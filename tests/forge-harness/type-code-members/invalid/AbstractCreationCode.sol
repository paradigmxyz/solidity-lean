// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract A {}

contract AbstractCreationCode {
    function bad() external pure returns (bytes memory) {
        return type(A).creationCode;
    }
}
