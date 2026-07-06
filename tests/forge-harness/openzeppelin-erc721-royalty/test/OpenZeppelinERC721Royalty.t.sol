// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinERC721RoyaltyHarness,
    OpenZeppelinRoyaltyIERC165,
    OpenZeppelinRoyaltyIERC2981,
    OpenZeppelinRoyaltyIERC721,
    OpenZeppelinRoyaltyIERC721Metadata
} from "../src/OpenZeppelinERC721Royalty.sol";

contract OpenZeppelinERC721RoyaltyForgeTest {
    function testMetadataInterfacesAndDefaultRoyalty() public {
        OpenZeppelinERC721RoyaltyHarness token =
            new OpenZeppelinERC721RoyaltyHarness();

        require(
            keccak256(bytes(token.name())) == keccak256(bytes("Royalty NFT")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("RNFT")), "symbol");
        require(token.supportsInterface(type(OpenZeppelinRoyaltyIERC165).interfaceId), "erc165 id");
        require(token.supportsInterface(type(OpenZeppelinRoyaltyIERC721).interfaceId), "erc721 id");
        require(
            token.supportsInterface(type(OpenZeppelinRoyaltyIERC721Metadata).interfaceId),
            "metadata id"
        );
        require(token.supportsInterface(type(OpenZeppelinRoyaltyIERC2981).interfaceId), "royalty id");
        require(!token.supportsInterface(0xffffffff), "unknown id");

        (address receiver, uint256 amount) = token.royaltyInfo(777, 10000);
        require(receiver == address(0x4444), "default receiver");
        require(amount == 500, "default amount");

        (address oddReceiver, uint256 oddAmount) = token.royaltyInfo(777, 12345);
        require(oddReceiver == address(0x4444), "odd receiver");
        require(oddAmount == 617, "odd amount");
    }

    function testTokenRoyaltyOverridesResetAndDelete() public {
        OpenZeppelinERC721RoyaltyHarness token =
            new OpenZeppelinERC721RoyaltyHarness();

        token.setTokenRoyalty(1, address(0x5555), 1250);

        (address tokenReceiver, uint256 tokenAmount) =
            token.royaltyInfo(1, 20000);
        require(tokenReceiver == address(0x5555), "token receiver");
        require(tokenAmount == 2500, "token amount");

        (address defaultReceiver, uint256 defaultAmount) =
            token.royaltyInfo(2, 20000);
        require(defaultReceiver == address(0x4444), "default receiver");
        require(defaultAmount == 1000, "default amount");

        token.resetTokenRoyalty(1);
        (address resetReceiver, uint256 resetAmount) =
            token.royaltyInfo(1, 20000);
        require(resetReceiver == address(0x4444), "reset receiver");
        require(resetAmount == 1000, "reset amount");

        token.deleteDefaultRoyalty();
        (address deletedReceiver, uint256 deletedAmount) =
            token.royaltyInfo(2, 20000);
        require(deletedReceiver == address(0), "deleted receiver");
        require(deletedAmount == 0, "deleted amount");
    }

    function testBurnClearsTokenRoyaltyAndApproval() public {
        OpenZeppelinERC721RoyaltyHarness token =
            new OpenZeppelinERC721RoyaltyHarness();
        OpenZeppelinERC721RoyaltyActor actor =
            new OpenZeppelinERC721RoyaltyActor();

        token.mint(address(this), 7);
        token.setTokenRoyalty(7, address(0x7777), 2000);
        token.approve(address(actor), 7);
        actor.burnToken(token, 7);

        (address receiver, uint256 amount) = token.royaltyInfo(7, 10000);
        require(receiver == address(0x4444), "burn receiver");
        require(amount == 500, "burn amount");

        try token.ownerOf(7) returns (address) {
            revert("expected burned owner");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC721: invalid token ID")),
                "owner reason"
            );
        }

        try token.getApproved(7) returns (address) {
            revert("expected burned approval");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC721: invalid token ID")),
                "approval reason"
            );
        }
    }

    function testInvalidRoyaltyRollbacks() public {
        OpenZeppelinERC721RoyaltyHarness token =
            new OpenZeppelinERC721RoyaltyHarness();

        try token.setDefaultRoyalty(address(0xaaaa), 10001) {
            revert("expected default fee");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("ERC2981: royalty fee will exceed salePrice")
                    ),
                "default fee reason"
            );
        }

        (address receiver, uint256 amount) = token.royaltyInfo(1, 10000);
        require(receiver == address(0x4444), "default fee rollback receiver");
        require(amount == 500, "default fee rollback amount");

        try token.setDefaultRoyalty(address(0), 250) {
            revert("expected default receiver");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC2981: invalid receiver")),
                "default receiver reason"
            );
        }
        (receiver, amount) = token.royaltyInfo(1, 10000);
        require(receiver == address(0x4444), "default receiver rollback");
        require(amount == 500, "default receiver rollback amount");

        try token.setTokenRoyalty(1, address(0), 250) {
            revert("expected token receiver");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC2981: Invalid parameters")),
                "token receiver reason"
            );
        }
        (receiver, amount) = token.royaltyInfo(1, 10000);
        require(receiver == address(0x4444), "token receiver rollback");
        require(amount == 500, "token receiver rollback amount");
    }
}

contract OpenZeppelinERC721RoyaltyActor {
    function burnToken(OpenZeppelinERC721RoyaltyHarness token, uint256 tokenId)
        external
    {
        token.burn(tokenId);
    }
}
