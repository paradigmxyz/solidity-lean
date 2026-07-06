// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryCode {
    function bad(address target) external view returns (bytes memory) {
        return L(target).code;
    }
}
