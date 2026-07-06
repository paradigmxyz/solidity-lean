// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReceiveParam {
    receive(uint256 value) external payable {
        value;
    }
}
