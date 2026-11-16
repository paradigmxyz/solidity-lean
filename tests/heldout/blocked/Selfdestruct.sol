// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Selfdestruct {
    uint256 public x;

    function set(uint256 v) external {
        x = v;
    }

    function kill() external {
        selfdestruct(payable(msg.sender));
    }
}
