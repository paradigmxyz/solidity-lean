// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryParameter {
    function bad(L input) internal pure returns (uint256) {
        input;
        return 1;
    }
}
