// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinPaymentSplitter.sol";

interface Vm {
    function deal(address account, uint256 newBalance) external;
}

contract OpenZeppelinPaymentRejector {
    receive() external payable {
        revert("reject");
    }
}

contract OpenZeppelinPaymentSplitterForgeTest {
    Vm constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    receive() external payable {}

    function _payees(address first, address second)
        internal
        pure
        returns (address[] memory payees)
    {
        payees = new address[](2);
        payees[0] = first;
        payees[1] = second;
    }

    function _shares(uint256 first, uint256 second)
        internal
        pure
        returns (uint256[] memory shares_)
    {
        shares_ = new uint256[](2);
        shares_[0] = first;
        shares_[1] = second;
    }

    function testConstructorReceiveAndRelease() public {
        vm.deal(address(this), 100 ether);

        address payable alice = payable(address(0xA11CE));
        address payable bob = payable(address(0xB0B));

        OpenZeppelinPaymentSplitter splitter =
            new OpenZeppelinPaymentSplitter(_payees(alice, bob), _shares(1, 3));

        require(splitter.totalShares() == 4, "total shares");
        require(splitter.shares(alice) == 1, "alice shares");
        require(splitter.shares(bob) == 3, "bob shares");
        require(splitter.payee(0) == alice, "payee 0");
        require(splitter.payee(1) == bob, "payee 1");

        (bool paid, ) = address(splitter).call{value: 400}("");
        require(paid, "receive");

        require(splitter.releasable(alice) == 100, "alice releasable");
        require(splitter.releasable(bob) == 300, "bob releasable");

        uint256 aliceBefore = alice.balance;
        splitter.release(alice);
        require(alice.balance == aliceBefore + 100, "alice paid");
        require(splitter.released(alice) == 100, "alice released");
        require(splitter.totalReleased() == 100, "total released");
        require(splitter.releasable(alice) == 0, "alice drained");
        require(splitter.releasable(bob) == 300, "bob still due");

        uint256 bobBefore = bob.balance;
        splitter.release(bob);
        require(bob.balance == bobBefore + 300, "bob paid");
        require(splitter.released(bob) == 300, "bob released");
        require(splitter.totalReleased() == 400, "all released");
    }

    function testReleaseRevertsAndRollsBack() public {
        vm.deal(address(this), 100 ether);

        OpenZeppelinPaymentRejector rejector =
            new OpenZeppelinPaymentRejector();
        address payable rejectingPayee = payable(address(rejector));
        address payable otherPayee = payable(address(0xB0B));

        OpenZeppelinPaymentSplitter splitter =
            new OpenZeppelinPaymentSplitter(
                _payees(rejectingPayee, otherPayee),
                _shares(1, 1)
            );

        (bool paid, ) = address(splitter).call{value: 200}("");
        require(paid, "receive");

        try splitter.release(rejectingPayee) {
            revert("expected rejection");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes(
                            "Address: unable to send value, recipient may have reverted"
                        )
                    ),
                "reason"
            );
        }

        require(splitter.released(rejectingPayee) == 0, "released rollback");
        require(splitter.totalReleased() == 0, "total rollback");
        require(splitter.releasable(rejectingPayee) == 100, "still due");
    }

    function testConstructorRejectsBadPayees() public {
        try new OpenZeppelinPaymentSplitter(
            _payees(address(0), address(0xB0B)),
            _shares(1, 1)
        ) {
            revert("expected zero payee");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("PaymentSplitter: account is the zero address")),
                "zero reason"
            );
        }

        try new OpenZeppelinPaymentSplitter(
            _payees(address(0xA11CE), address(0xA11CE)),
            _shares(1, 1)
        ) {
            revert("expected duplicate payee");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("PaymentSplitter: account already has shares")),
                "duplicate reason"
            );
        }
    }
}
