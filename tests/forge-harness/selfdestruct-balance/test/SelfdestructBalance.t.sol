// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {SelfdestructBalance, Sink} from "../src/SelfdestructBalance.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for the selfdestruct balance
/// transfer (gap CS1): the contract's whole balance moves to the recipient and
/// the contract's own balance is zeroed.
contract SelfdestructBalanceForgeTest {
    receive() external payable {}

    /// A distinct recipient is credited the full balance; self goes to 0.
    function testTransferCreditsRecipient() public {
        Sink s = new Sink();
        SelfdestructBalance b = new SelfdestructBalance{value: 100}();
        uint256 before = address(s).balance;
        b.blow(address(s));
        require(address(b).balance == 0, "self zeroed");
        require(address(s).balance == before + 100, "recipient credited");
    }

    /// selfdestruct-to-self edge: the balance ends at 0 (same-tx account).
    function testSelfRecipientEdge() public {
        SelfdestructBalance b = new SelfdestructBalance{value: 77}();
        b.blowSelf();
        require(address(b).balance == 0, "self-recipient zero");
    }
}
