// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Intra-frame balance accounting (gap A2): `msg.value` credits the callee
/// before body execution, `address(this).balance` reads the dynamic self
/// balance, and a successful value-carrying call debits it (a failed one does
/// not — the EVM refunds).
contract BalanceAccounting {
    uint256 public deployBalance;

    constructor() payable {
        // Constructor entry is credited with msg.value before the body runs.
        deployBalance = address(this).balance;
    }

    /// The received value shows up in `address(this).balance` within the frame.
    function creditAndRead() external payable returns (uint256) {
        return address(this).balance;
    }

    /// A successful value send debits the self balance (observed by the read).
    function sendThenRead(address to, uint256 amt)
        external
        payable
        returns (uint256)
    {
        bool ok = payable(to).send(amt);
        require(ok, "send failed");
        return address(this).balance;
    }

    /// A failed value send does not debit (the value is refunded).
    function trySendThenRead(address to, uint256 amt)
        external
        payable
        returns (uint256 bal, bool ok)
    {
        ok = payable(to).send(amt);
        bal = address(this).balance;
    }
}

/// Recipient that rejects value (reverts in receive), forcing a failed send.
contract BalanceRejector {
    receive() external payable {
        revert("no");
    }
}
