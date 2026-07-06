// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad(int256 length) external pure returns (uint256) {
        string memory data = new string(length);
        data;
        return 1;
    }
}
