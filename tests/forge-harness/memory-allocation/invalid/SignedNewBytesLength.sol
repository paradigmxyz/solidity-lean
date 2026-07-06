// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad(int256 length) external pure returns (uint256) {
        bytes memory data = new bytes(length);
        data;
        return 1;
    }
}
