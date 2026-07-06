// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryLocal {
    function bad(address input) external pure returns (address) {
        L value = L(input);
        return address(value);
    }
}
