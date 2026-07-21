// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EventOverloadHarnessTarget {
    event E(uint256 v);
    event E(address who);

    function fireWord() external {
        uint256 v = 5;
        emit E(v);
    }

    function fireAddr(address a) external {
        emit E(a);
    }
}
