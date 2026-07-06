// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TryArrayPush {
    uint256[] private values;

    function bad() external returns (uint256) {
        try values.push(1) {
            return 1;
        } catch {
            return 0;
        }
    }
}
