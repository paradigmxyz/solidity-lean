// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryBalance {
    function bad(address target) external view returns (uint256) {
        return L(target).balance;
    }
}
