// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (string memory) {
        return string.concat(bytes("x"));
    }
}
