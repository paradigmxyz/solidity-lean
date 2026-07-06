// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MaybeLoopReturn {
    uint256[] private stored;

    function bad(bool run) internal returns (uint256[] storage result) {
        while (run) {
            result = stored;
            break;
        }
    }
}
