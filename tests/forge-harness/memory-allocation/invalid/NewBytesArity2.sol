// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (uint256) {
        bytes memory data = new bytes(1, 2);
        data;
        return 1;
    }
}
