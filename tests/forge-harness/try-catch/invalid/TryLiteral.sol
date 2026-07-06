// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TryLiteral {
    function bad() external returns (uint256) {
        try 1 {
            return 1;
        } catch {
            return 0;
        }
    }
}
