// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract ViewAndPure {
    uint256 public x = 1;

    // Promise not to modify the state.
    /// @custom:succeeds-if msg.value == 0 && x + y <= type(uint256).max
    /// @custom:ensures result == x + y
    function addToX(uint256 y) public view returns (uint256) {
        return x + y;
    }

    // Promise not to modify or read from the state.
    /// @custom:succeeds-if msg.value == 0 && i + j <= type(uint256).max
    /// @custom:ensures result == i + j
    function add(uint256 i, uint256 j) public pure returns (uint256) {
        return i + j;
    }
}
