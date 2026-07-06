// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PureStateRead {
    uint256 private x;

    function readPure() external pure returns (uint256) {
        return x;
    }
}
