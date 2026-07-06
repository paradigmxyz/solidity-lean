// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PureModifierStateRead {
    uint256 private x;

    modifier readsState() {
        x;
        _;
    }

    function pureWithReadModifier() external pure readsState returns (uint256) {
        return 1;
    }
}
