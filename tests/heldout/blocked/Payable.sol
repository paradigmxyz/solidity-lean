// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Payable {
    uint256 public total;

    /// @notice ensures total == old(total) + msg.value
    function deposit() external payable {
        total += msg.value;
    }
}
