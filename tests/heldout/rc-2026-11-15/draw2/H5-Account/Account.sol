// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract Account {
    uint256 public balance;
    uint256 public constant MAX_UINT = 2 ** 256 - 1;

    /// @custom:succeeds-if msg.value == 0 && balance + _amount <= type(uint256).max
    /// @custom:ensures balance == old(balance) + _amount
    function deposit(uint256 _amount) public {
        uint256 oldBalance = balance;
        uint256 newBalance = balance + _amount;

        // balance + _amount does not overflow if balance + _amount >= balance
        require(newBalance >= oldBalance, "Overflow");

        balance = newBalance;

        assert(balance >= oldBalance);
    }

    /// @custom:succeeds-if msg.value == 0 && _amount <= balance
    /// @custom:ensures balance == old(balance) - _amount
    function withdraw(uint256 _amount) public {
        uint256 oldBalance = balance;

        // balance - _amount does not underflow if balance >= _amount
        require(balance >= _amount, "Underflow");

        if (balance < _amount) {
            revert("Underflow");
        }

        balance -= _amount;

        assert(balance <= oldBalance);
    }
}
