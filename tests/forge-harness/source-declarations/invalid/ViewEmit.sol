// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ViewEmit {
    event Ping();

    function viewEmit() external view {
        emit Ping();
    }
}
