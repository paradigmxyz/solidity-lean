// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC20CappedPausableHarness
} from "../src/OpenZeppelinERC20CappedPausable.sol";

contract OpenZeppelinERC20CappedPausableForgeTest {
    function testConstructorOwnerCapMetadataAndMint() public {
        OpenZeppelinERC20CappedPausableHarness token =
            new OpenZeppelinERC20CappedPausableHarness(150);

        require(token.owner() == address(this), "owner");
        require(token.cap() == 150, "cap");
        require(
            keccak256(bytes(token.name())) ==
                keccak256(bytes("Capped Pausable")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("CPZ")), "symbol");
        require(token.decimals() == 18, "decimals");
        require(!token.paused(), "initial paused");

        token.mint(address(this), 100);
        require(token.totalSupply() == 100, "supply");
        require(token.balanceOf(address(this)) == 100, "balance");
        require(token.transfer(address(0xB0B), 25), "transfer");
        require(token.balanceOf(address(this)) == 75, "sender");
        require(token.balanceOf(address(0xB0B)) == 25, "recipient");
    }

    function testCapExceededRollsBack() public {
        OpenZeppelinERC20CappedPausableHarness token =
            new OpenZeppelinERC20CappedPausableHarness(150);

        token.mint(address(this), 100);

        try token.mint(address(0xB0B), 60) {
            revert("expected cap revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Capped: cap exceeded")),
                "cap reason"
            );
        }

        require(token.totalSupply() == 100, "supply rollback");
        require(token.balanceOf(address(this)) == 100, "owner rollback");
        require(token.balanceOf(address(0xB0B)) == 0, "bob rollback");
    }

    function testPauseBlocksTransferMintBurnAndUnpauseRestores() public {
        OpenZeppelinERC20CappedPausableHarness token =
            new OpenZeppelinERC20CappedPausableHarness(150);

        token.mint(address(this), 100);
        token.pause();
        require(token.paused(), "paused");

        try token.transfer(address(0xB0B), 1) returns (bool) {
            revert("expected paused transfer");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Pausable: token transfer while paused")),
                "transfer reason"
            );
        }

        try token.mint(address(0xB0B), 1) {
            revert("expected paused mint");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Pausable: token transfer while paused")),
                "mint reason"
            );
        }

        try token.burn(1) {
            revert("expected paused burn");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Pausable: token transfer while paused")),
                "burn reason"
            );
        }

        require(token.totalSupply() == 100, "paused supply");
        require(token.balanceOf(address(this)) == 100, "paused balance");

        token.unpause();
        require(!token.paused(), "unpaused");
        require(token.transfer(address(0xB0B), 10), "transfer after");
        token.burn(5);
        require(token.totalSupply() == 95, "supply after");
        require(token.balanceOf(address(this)) == 85, "balance after");
    }

    function testOnlyOwnerPauseAndTransferOwnership() public {
        OpenZeppelinERC20CappedPausableHarness token =
            new OpenZeppelinERC20CappedPausableHarness(150);
        OpenZeppelinERC20CappedPausableActor actor =
            new OpenZeppelinERC20CappedPausableActor();

        try actor.pauseToken(token) {
            revert("expected owner revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("Ownable: caller is not the owner")),
                "owner reason"
            );
        }

        require(!token.paused(), "still unpaused");
        token.transferOwnership(address(actor));
        require(token.owner() == address(actor), "new owner");
        actor.pauseToken(token);
        require(token.paused(), "actor paused");
        actor.unpauseToken(token);
        require(!token.paused(), "actor unpaused");
        actor.mintToken(token, address(0xB0B), 7);
        require(token.balanceOf(address(0xB0B)) == 7, "actor mint");
    }
}

contract OpenZeppelinERC20CappedPausableActor {
    function pauseToken(OpenZeppelinERC20CappedPausableHarness token) external {
        token.pause();
    }

    function unpauseToken(OpenZeppelinERC20CappedPausableHarness token)
        external
    {
        token.unpause();
    }

    function mintToken(
        OpenZeppelinERC20CappedPausableHarness token,
        address account,
        uint256 amount
    ) external {
        token.mint(account, amount);
    }
}
