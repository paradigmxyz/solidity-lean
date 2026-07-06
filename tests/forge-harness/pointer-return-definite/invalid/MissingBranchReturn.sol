// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MissingBranchReturn {
    uint256[] private stored;

    function bad(bool pick) internal returns (uint256[] storage result) {
        if (pick) {
            result = stored;
        }
    }
}
