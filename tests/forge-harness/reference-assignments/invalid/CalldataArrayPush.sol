// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract CalldataArrayPush {
    function bad(uint256[] calldata input) external pure {
        input.push(1);
    }
}
