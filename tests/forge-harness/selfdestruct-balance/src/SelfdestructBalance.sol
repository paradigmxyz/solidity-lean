// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// selfdestruct(recipient) moves the contract's ENTIRE balance to `recipient`
/// (gap CS1). EIP-6780 only governs whether the account is deleted; the balance
/// transfer is unconditional.
contract SelfdestructBalance {
    constructor() payable {}

    /// Send the whole balance to a distinct recipient and self-destruct.
    function blow(address recipient) external {
        selfdestruct(payable(recipient));
    }

    /// selfdestruct-to-self edge.
    function blowSelf() external {
        selfdestruct(payable(address(this)));
    }

    receive() external payable {}
}

/// Value-accepting recipient for the Forge side.
contract Sink {
    receive() external payable {}
}
