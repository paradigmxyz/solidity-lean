// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BytesPushWrongType {
    bytes private data;

    function bad() external {
        data.push(bytes2(0x0708));
    }
}
