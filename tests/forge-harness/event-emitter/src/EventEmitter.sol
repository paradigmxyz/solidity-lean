// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EventEmitterHarnessTarget {
    event Hit(uint256 indexed key, uint256 value);

    function fire(uint256 key, uint256 value) external {
        emit Hit(key, value);
    }
}
