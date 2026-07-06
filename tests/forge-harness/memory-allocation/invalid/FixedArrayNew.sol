// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (uint256) {
        uint256[3] memory values = new uint256[3](3);
        values;
        return 1;
    }
}
