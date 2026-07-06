// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinRefundEscrow.sol";

interface Vm {
    function deal(address account, uint256 newBalance) external;
}

contract OpenZeppelinRefundEscrowStranger {
    function close(OpenZeppelinRefundEscrow escrow) external {
        escrow.close();
    }

    function deposit(OpenZeppelinRefundEscrow escrow, address refundee)
        external
        payable
    {
        escrow.deposit{value: msg.value}(refundee);
    }
}

contract OpenZeppelinRefundRejector {
    receive() external payable {
        revert("reject");
    }
}

contract OpenZeppelinRefundEscrowForgeTest {
    Vm constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    receive() external payable {}

    function testConstructorAndRefundFlow() public {
        vm.deal(address(this), 100 ether);

        address payable beneficiary = payable(address(0xBEEF));
        address payable alice = payable(address(0xA11CE));
        address payable bob = payable(address(0xB0B));

        OpenZeppelinRefundEscrow escrow =
            new OpenZeppelinRefundEscrow(beneficiary);

        require(escrow.owner() == address(this), "owner");
        require(escrow.beneficiary() == beneficiary, "beneficiary");
        require(uint256(escrow.state()) == 0, "active");
        require(!escrow.withdrawalAllowed(alice), "active refund");

        escrow.deposit{value: 70}(alice);
        escrow.deposit{value: 30}(bob);
        require(escrow.depositsOf(alice) == 70, "alice deposit");
        require(escrow.depositsOf(bob) == 30, "bob deposit");

        OpenZeppelinRefundEscrowStranger stranger =
            new OpenZeppelinRefundEscrowStranger();
        try stranger.close(escrow) {
            revert("expected only owner");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("Ownable: caller is not the owner")),
                "only owner reason"
            );
        }
        require(uint256(escrow.state()) == 0, "only owner rollback");

        escrow.enableRefunds();
        require(uint256(escrow.state()) == 1, "refunding");
        require(escrow.withdrawalAllowed(alice), "refund allowed");

        uint256 aliceBefore = alice.balance;
        escrow.withdraw(alice);
        require(alice.balance == aliceBefore + 70, "alice refunded");
        require(escrow.depositsOf(alice) == 0, "alice cleared");
        require(escrow.depositsOf(bob) == 30, "bob remains");

        try stranger.deposit{value: 1}(escrow, alice) {
            revert("expected deposit closed");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("RefundEscrow: can only deposit while active")
                    ),
                "closed deposit reason"
            );
        }
    }

    function testCloseAndBeneficiaryWithdraw() public {
        vm.deal(address(this), 100 ether);

        address payable beneficiary = payable(address(0xBEEF));
        OpenZeppelinRefundEscrow escrow =
            new OpenZeppelinRefundEscrow(beneficiary);

        escrow.deposit{value: 125}(address(0xCAFE));
        escrow.close();
        require(uint256(escrow.state()) == 2, "closed");
        require(!escrow.withdrawalAllowed(address(0xCAFE)), "no refund");

        uint256 beneficiaryBefore = beneficiary.balance;
        escrow.beneficiaryWithdraw();
        require(
            beneficiary.balance == beneficiaryBefore + 125,
            "beneficiary paid"
        );
    }

    function testRejectedRefundRollsBack() public {
        vm.deal(address(this), 100 ether);

        address payable beneficiary = payable(address(0xBEEF));
        OpenZeppelinRefundRejector rejector = new OpenZeppelinRefundRejector();
        address payable rejectingPayee = payable(address(rejector));

        OpenZeppelinRefundEscrow escrow =
            new OpenZeppelinRefundEscrow(beneficiary);
        escrow.deposit{value: 44}(rejectingPayee);
        escrow.enableRefunds();

        try escrow.withdraw(rejectingPayee) {
            revert("expected rejected refund");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes(
                            "Address: unable to send value, recipient may have reverted"
                        )
                    ),
                "rejected refund reason"
            );
        }

        require(escrow.depositsOf(rejectingPayee) == 44, "rollback");
    }

    function testConstructorRejectsZeroBeneficiary() public {
        try new OpenZeppelinRefundEscrow(payable(address(0))) {
            revert("expected zero beneficiary");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("RefundEscrow: beneficiary is the zero address")
                    ),
                "zero beneficiary reason"
            );
        }
    }
}
