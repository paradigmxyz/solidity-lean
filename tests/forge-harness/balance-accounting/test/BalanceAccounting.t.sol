// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {BalanceAccounting, BalanceRejector} from "../src/BalanceAccounting.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for intra-frame balance accounting.
contract BalanceAccountingForgeTest {
    receive() external payable {}

    /// Constructor credit: a value-funded deploy sees its balance in the ctor.
    function testConstructorCredit() public {
        BalanceAccounting b = new BalanceAccounting{value: 3}();
        require(b.deployBalance() == 3, "ctor credit");
    }

    /// Function credit: msg.value is added to the pre-existing balance.
    function testFunctionCredit() public {
        BalanceAccounting b = new BalanceAccounting{value: 3}();
        uint256 seen = b.creditAndRead{value: 5}();
        require(seen == 8, "credit read");
    }

    /// Successful send debits the self balance.
    function testSuccessfulSendDebits() public {
        BalanceAccounting b = new BalanceAccounting{value: 10}();
        uint256 seen = b.sendThenRead(address(this), 4);
        require(seen == 6, "debit read");
    }

    /// Failed send leaves the balance un-debited (value refunded).
    function testRejectedSendNoDebit() public {
        BalanceAccounting b = new BalanceAccounting{value: 10}();
        BalanceRejector r = new BalanceRejector();
        (uint256 bal, bool ok) = b.trySendThenRead(address(r), 4);
        require(!ok, "send should fail");
        require(bal == 10, "no debit");
    }
}
