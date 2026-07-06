// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ViewModifierStateWrite {
    uint256 private x;

    modifier writesState() {
        x = 5;
        _;
    }

    function viewWithWriteModifier() external view writesState returns (uint256) {
        return 1;
    }
}
