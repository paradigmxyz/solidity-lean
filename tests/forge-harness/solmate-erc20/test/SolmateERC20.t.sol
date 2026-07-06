// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.8.20;

import {
    SolmateERC20Harness,
    SolmateERC20Spender
} from "../src/SolmateERC20.sol";

interface Vm {
    function addr(uint256 privateKey) external returns (address);
    function sign(uint256 privateKey, bytes32 digest)
        external
        returns (uint8 v, bytes32 r, bytes32 s);
}

contract SolmateERC20ForgeTest {
    Vm constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testConstructorMetadataAndDomainSeparator() public {
        SolmateERC20Harness token =
            new SolmateERC20Harness("Solmate Token", "SMT", 18);

        require(
            keccak256(bytes(token.name())) == keccak256(bytes("Solmate Token")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("SMT")), "symbol");
        require(token.decimals() == 18, "decimals");
        require(token.totalSupply() == 0, "supply");
        require(
            token.DOMAIN_SEPARATOR() == token.exposedComputeDomainSeparator(),
            "domain"
        );
    }

    function testMintBurnTransferAndAllowance() public {
        SolmateERC20Harness token =
            new SolmateERC20Harness("Solmate Token", "SMT", 18);
        SolmateERC20Spender spender = new SolmateERC20Spender();

        address recipient = address(0xBEEF);
        address delegatedRecipient = address(0xCAFE);

        token.mint(address(this), 100);
        require(token.totalSupply() == 100, "mint supply");
        require(token.balanceOf(address(this)) == 100, "mint balance");

        require(token.transfer(recipient, 30), "transfer");
        require(token.balanceOf(address(this)) == 70, "sender balance");
        require(token.balanceOf(recipient) == 30, "receiver balance");

        require(token.approve(address(spender), 25), "approve");
        require(
            token.allowance(address(this), address(spender)) == 25,
            "allowance"
        );
        require(
            spender.transferFromToken(
                token,
                address(this),
                delegatedRecipient,
                10
            ),
            "transferFrom"
        );
        require(
            token.allowance(address(this), address(spender)) == 15,
            "allowance spent"
        );
        require(token.balanceOf(address(this)) == 60, "owner after spend");
        require(token.balanceOf(delegatedRecipient) == 10, "delegated recipient");

        require(token.approve(address(spender), type(uint256).max), "max approve");
        require(
            spender.transferFromToken(token, address(this), delegatedRecipient, 5),
            "max transferFrom"
        );
        require(
            token.allowance(address(this), address(spender)) == type(uint256).max,
            "max allowance kept"
        );

        token.burn(address(this), 5);
        require(token.totalSupply() == 95, "burn supply");
        require(token.balanceOf(address(this)) == 50, "burn balance");
    }

    function testPermit() public {
        SolmateERC20Harness token =
            new SolmateERC20Harness("Solmate Token", "SMT", 18);

        uint256 ownerKey = 0xA11CE;
        address owner = vm.addr(ownerKey);
        address spender = address(0xB0B);
        uint256 value = 77;
        uint256 deadline = block.timestamp + 1;

        bytes32 structHash = keccak256(
            abi.encode(
                keccak256(
                    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"
                ),
                owner,
                spender,
                value,
                token.nonces(owner),
                deadline
            )
        );
        bytes32 digest = keccak256(
            abi.encodePacked("\x19\x01", token.DOMAIN_SEPARATOR(), structHash)
        );
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerKey, digest);

        token.permit(owner, spender, value, deadline, v, r, s);

        require(token.nonces(owner) == 1, "nonce");
        require(token.allowance(owner, spender) == value, "permit allowance");
    }

    function testPermitDeadlineAndTransferRollback() public {
        SolmateERC20Harness token =
            new SolmateERC20Harness("Solmate Token", "SMT", 18);

        try token.permit(address(0xA11CE), address(0xB0B), 1, 0, 27, 0, 0) {
            revert("expected expired permit");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("PERMIT_DEADLINE_EXPIRED")),
                "expired reason"
            );
        }

        token.mint(address(this), 3);
        try token.transfer(address(0xBEEF), 4) returns (bool) {
            revert("expected transfer underflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "panic code");
        }
        require(token.balanceOf(address(this)) == 3, "rollback sender");
        require(token.balanceOf(address(0xBEEF)) == 0, "rollback receiver");
    }
}
