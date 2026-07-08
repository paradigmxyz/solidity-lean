// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// C3: packed mode forbids an array whose element is dynamically sized.
contract C3PackedBytesArray {
    function f(bytes[] memory a) public pure returns (bytes memory) {
        return abi.encodePacked(a);
    }
}
