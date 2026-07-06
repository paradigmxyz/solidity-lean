// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract CalldataArrayPop {
    function bad(uint256[] calldata input) external pure {
        input.pop();
    }
}
