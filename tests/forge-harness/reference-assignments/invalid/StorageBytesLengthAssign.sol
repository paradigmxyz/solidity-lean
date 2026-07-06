// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageBytesLengthAssign {
    bytes private data;

    function bad() external {
        data.length = 1;
    }
}
