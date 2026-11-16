// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract SimpleStorage {
    // State variable to store a number
    uint256 public num;

    // You need to send a transaction to write to a state variable.
    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures num == _num
    function set(uint256 _num) public {
        num = _num;
    }

    // You can read from a state variable without sending a transaction.
    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures result == num
    function get() public view returns (uint256) {
        return num;
    }
}
