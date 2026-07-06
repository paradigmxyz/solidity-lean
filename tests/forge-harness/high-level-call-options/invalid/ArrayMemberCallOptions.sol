// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    uint256[] private items;

    function bad() external {
        items.push{gas: 1}(3);
    }
}
