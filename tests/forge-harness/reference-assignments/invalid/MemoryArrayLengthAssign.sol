// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryArrayLengthAssign {
    function bad(uint256[] memory input) public pure {
        input.length = 1;
    }
}
