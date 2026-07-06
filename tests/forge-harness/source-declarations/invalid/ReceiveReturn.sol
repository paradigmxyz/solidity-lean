// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReceiveReturn {
    receive() external payable returns (uint256) {
        return 1;
    }
}
