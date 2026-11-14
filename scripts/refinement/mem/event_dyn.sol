// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract EventDyn {
    event Note(address indexed who, bytes data);

    function note(bytes calldata data) external {
        emit Note(msg.sender, data);
    }
}
