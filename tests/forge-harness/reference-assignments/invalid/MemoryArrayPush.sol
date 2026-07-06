// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryArrayPush {
    function bad(uint256[] memory input) public pure {
        input.push(1);
    }
}
