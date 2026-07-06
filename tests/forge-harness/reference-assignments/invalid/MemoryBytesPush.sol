// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryBytesPush {
    function bad(bytes memory data) public pure {
        data.push(bytes1(uint8(1)));
    }
}
