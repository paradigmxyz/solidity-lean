// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MultipleReceive {
    receive() external payable {}
    receive() external payable {}
}
