// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad(int256 length) external pure returns (uint256) {
        uint256[] memory values = new uint256[](length);
        values;
        return 1;
    }
}
