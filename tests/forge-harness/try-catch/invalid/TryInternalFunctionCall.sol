// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TryInternalFunctionCall {
    function f() internal pure returns (uint256) {
        return 1;
    }

    function bad() external returns (uint256) {
        try f() returns (uint256 value) {
            return value;
        } catch {
            return 0;
        }
    }
}
