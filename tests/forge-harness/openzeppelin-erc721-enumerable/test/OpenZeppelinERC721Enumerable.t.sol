// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC721EnumerableHarness,
    OpenZeppelinEnumerableIERC165,
    OpenZeppelinEnumerableIERC721,
    OpenZeppelinEnumerableIERC721Enumerable,
    OpenZeppelinEnumerableIERC721Metadata
} from "../src/OpenZeppelinERC721Enumerable.sol";

contract OpenZeppelinERC721EnumerableForgeTest {
    function testMetadataInterfaceIdsAndMintEnumeration() public {
        OpenZeppelinERC721EnumerableHarness token =
            new OpenZeppelinERC721EnumerableHarness();

        require(
            keccak256(bytes(token.name())) == keccak256(bytes("Enumerable NFT")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("ENFT")), "symbol");
        require(token.supportsInterface(type(OpenZeppelinEnumerableIERC165).interfaceId), "erc165 id");
        require(token.supportsInterface(type(OpenZeppelinEnumerableIERC721).interfaceId), "erc721 id");
        require(
            token.supportsInterface(
                type(OpenZeppelinEnumerableIERC721Metadata).interfaceId
            ),
            "metadata id"
        );
        require(
            token.supportsInterface(
                type(OpenZeppelinEnumerableIERC721Enumerable).interfaceId
            ),
            "enumerable id"
        );
        require(!token.supportsInterface(0xffffffff), "unknown id");

        token.mint(address(this), 1);
        token.mint(address(this), 2);
        token.mint(address(0xb0b), 3);

        require(token.totalSupply() == 3, "supply");
        require(token.tokenByIndex(0) == 1, "global 0");
        require(token.tokenByIndex(1) == 2, "global 1");
        require(token.tokenByIndex(2) == 3, "global 2");
        require(token.tokenOfOwnerByIndex(address(this), 0) == 1, "owner 0");
        require(token.tokenOfOwnerByIndex(address(this), 1) == 2, "owner 1");
        require(token.tokenOfOwnerByIndex(address(0xb0b), 0) == 3, "bob 0");
    }

    function testTransferUpdatesOwnerEnumerationBySwapAndPop() public {
        OpenZeppelinERC721EnumerableHarness token =
            new OpenZeppelinERC721EnumerableHarness();

        token.mint(address(this), 1);
        token.mint(address(this), 2);
        token.mint(address(this), 3);

        token.transferFrom(address(this), address(0xb0b), 2);

        require(token.balanceOf(address(this)) == 2, "sender balance");
        require(token.balanceOf(address(0xb0b)) == 1, "bob balance");
        require(token.ownerOf(2) == address(0xb0b), "owner");
        require(token.tokenOfOwnerByIndex(address(this), 0) == 1, "owner 0");
        require(token.tokenOfOwnerByIndex(address(this), 1) == 3, "owner 1");
        require(token.tokenOfOwnerByIndex(address(0xb0b), 0) == 2, "bob 0");
        require(token.tokenByIndex(0) == 1, "global 0");
        require(token.tokenByIndex(1) == 2, "global 1");
        require(token.tokenByIndex(2) == 3, "global 2");
    }

    function testApprovedBurnUpdatesOwnerAndGlobalEnumeration() public {
        OpenZeppelinERC721EnumerableHarness token =
            new OpenZeppelinERC721EnumerableHarness();
        OpenZeppelinERC721EnumerableActor actor =
            new OpenZeppelinERC721EnumerableActor();

        token.mint(address(this), 10);
        token.mint(address(this), 20);
        token.mint(address(this), 30);

        token.approve(address(actor), 20);
        actor.burnToken(token, 20);

        require(token.totalSupply() == 2, "supply");
        require(token.balanceOf(address(this)) == 2, "owner balance");
        require(token.tokenByIndex(0) == 10, "global 0");
        require(token.tokenByIndex(1) == 30, "global 1");
        require(token.tokenOfOwnerByIndex(address(this), 0) == 10, "owner 0");
        require(token.tokenOfOwnerByIndex(address(this), 1) == 30, "owner 1");

        try token.ownerOf(20) returns (address) {
            revert("expected burned");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC721: invalid token ID")),
                "burn reason"
            );
        }

        try token.tokenByIndex(2) returns (uint256) {
            revert("expected global bounds");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("ERC721Enumerable: global index out of bounds")
                    ),
                "global reason"
            );
        }
    }

    function testEnumerationRevertRollback() public {
        OpenZeppelinERC721EnumerableHarness token =
            new OpenZeppelinERC721EnumerableHarness();

        token.mint(address(this), 7);

        try token.mint(address(0xb0b), 7) {
            revert("expected duplicate");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC721: token already minted")),
                "duplicate reason"
            );
        }
        require(token.totalSupply() == 1, "duplicate rollback supply");
        require(token.ownerOf(7) == address(this), "duplicate rollback owner");

        try token.tokenOfOwnerByIndex(address(this), 1) returns (uint256) {
            revert("expected owner bounds");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("ERC721Enumerable: owner index out of bounds")
                    ),
                "owner reason"
            );
        }

        try token.forceBatchHook(address(0), address(this), 9, 2) {
            revert("expected batch rejection");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes(
                            "ERC721Enumerable: consecutive transfers not supported"
                        )
                    ),
                "batch reason"
            );
        }
        require(token.totalSupply() == 1, "batch rollback supply");
        require(token.tokenByIndex(0) == 7, "batch rollback token");
    }
}

contract OpenZeppelinERC721EnumerableActor {
    function burnToken(
        OpenZeppelinERC721EnumerableHarness token,
        uint256 tokenId
    ) external {
        token.burn(tokenId);
    }
}
