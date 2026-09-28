// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

contract SelectorReceiverSideEffect {
    uint256 public x;

    function f() external returns (uint256) {
        h().f.selector;
        return x;
    }

    function selectorValue() external returns (uint32) {
        return uint32(h().f.selector);
    }

    function h() public returns (SelectorReceiverSideEffect) {
        x = 42;
        return this;
    }
}
