// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryBytesPop {
    function bad(bytes memory data) public pure {
        data.pop();
    }
}
