// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract C3PackedStringArray {
    function f(string[] memory a) public pure returns (bytes memory) {
        return abi.encodePacked(a);
    }
}
