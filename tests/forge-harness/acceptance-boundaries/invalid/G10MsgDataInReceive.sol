// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G10: `msg.data` inside a receive function — solc TypeError 7139.
contract G10Bad {
    bytes stored;

    receive() external payable {
        stored = msg.data;
    }
}
