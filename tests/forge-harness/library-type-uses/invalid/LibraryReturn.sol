// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryReturn {
    function bad(address input) internal pure returns (L) {
        return L(input);
    }
}
