// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ViewStateWrite {
    uint256 private x;

    function writeView() external view returns (uint256) {
        x = 2;
        return 1;
    }
}
