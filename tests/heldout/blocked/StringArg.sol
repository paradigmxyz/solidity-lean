// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract StringArg {
    uint256 public len;

    /// @notice ensures len == bytes(s).length
    function set(string calldata s) external {
        len = bytes(s).length;
    }
}
