// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract UnknownEventEmit {
    function fire() external {
        emit Missing(1);
    }
}
