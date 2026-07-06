// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AnonymousEventSelector {
    event Hidden(uint256 value) anonymous;

    function selector() external pure returns (bytes32) {
        return Hidden.selector;
    }
}
