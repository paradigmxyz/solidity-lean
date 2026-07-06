// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC721CoreHarness,
    OpenZeppelinERC721CoreSpender,
    OpenZeppelinIERC721Core,
    OpenZeppelinIERC721Errors,
    OpenZeppelinIERC721MetadataCore
} from "../src/OpenZeppelinERC721Core.sol";

contract OpenZeppelinERC721CoreForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testMetadataInterfaceIdsAndMintEvent() public {
        OpenZeppelinERC721CoreHarness token =
            new OpenZeppelinERC721CoreHarness();

        require(
            keccak256(bytes(token.name())) == keccak256(bytes("Harness NFT")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("HNFT")), "symbol");
        require(token.supportsInterface(type(OpenZeppelinIERC721Core).interfaceId), "core id");
        require(
            token.supportsInterface(
                type(OpenZeppelinIERC721MetadataCore).interfaceId
            ),
            "metadata id"
        );
        require(token.supportsInterface(0x01ffc9a7), "erc165 id");
        require(!token.supportsInterface(0xffffffff), "unknown id");

        token.mint(address(this), 1);
        require(token.balanceOf(address(this)) == 1, "mint balance");
        require(token.ownerOf(1) == address(this), "mint owner");
        require(
            keccak256(bytes(token.tokenURI(1))) == keccak256(bytes("")),
            "empty uri"
        );
    }

    function testApproveTransferAndClearApproval() public {
        OpenZeppelinERC721CoreHarness token =
            new OpenZeppelinERC721CoreHarness();
        OpenZeppelinERC721CoreSpender spender =
            new OpenZeppelinERC721CoreSpender();

        token.mint(address(this), 1);
        token.approve(address(spender), 1);
        require(token.getApproved(1) == address(spender), "approved");

        spender.transferFromToken(token, address(this), address(0xbeef), 1);
        require(token.ownerOf(1) == address(0xbeef), "transferred owner");
        require(token.balanceOf(address(this)) == 0, "sender balance");
        require(token.balanceOf(address(0xbeef)) == 1, "recipient balance");
        require(token.getApproved(1) == address(0), "approval cleared");
    }

    function testOperatorApprovalTransferAndUnset() public {
        OpenZeppelinERC721CoreHarness token =
            new OpenZeppelinERC721CoreHarness();
        OpenZeppelinERC721CoreSpender spender =
            new OpenZeppelinERC721CoreSpender();

        token.mint(address(this), 2);
        token.setApprovalForAll(address(spender), true);
        require(
            token.isApprovedForAll(address(this), address(spender)),
            "operator approved"
        );
        spender.transferFromToken(token, address(this), address(0xcafe), 2);
        require(token.ownerOf(2) == address(0xcafe), "operator transfer");

        token.setApprovalForAll(address(spender), false);
        require(
            !token.isApprovedForAll(address(this), address(spender)),
            "operator unset"
        );
    }

    function testCoreErrorSelectorsAndRollback() public {
        OpenZeppelinERC721CoreHarness token =
            new OpenZeppelinERC721CoreHarness();

        try token.balanceOf(address(0)) returns (uint256) {
            revert("expected invalid owner");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721InvalidOwner.selector,
                    address(0)
                )
            );
        }

        try token.ownerOf(99) returns (address) {
            revert("expected nonexistent");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721NonexistentToken.selector,
                    99
                )
            );
        }

        try token.mint(address(0), 1) {
            revert("expected invalid receiver");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721InvalidReceiver.selector,
                    address(0)
                )
            );
        }
        require(token.balanceOf(address(this)) == 0, "mint rollback");
    }

    function testUnauthorizedWrongOwnerDuplicateAndBurn() public {
        OpenZeppelinERC721CoreHarness token =
            new OpenZeppelinERC721CoreHarness();

        token.mint(address(0xa11ce), 7);

        try token.transferFrom(address(0xa11ce), address(0xbeef), 7) {
            revert("expected insufficient approval");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors
                        .ERC721InsufficientApproval
                        .selector,
                    address(this),
                    7
                )
            );
        }

        token.mint(address(this), 8);
        try token.transferFrom(address(0xa11ce), address(0xbeef), 8) {
            revert("expected incorrect owner");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721IncorrectOwner.selector,
                    address(0xa11ce),
                    8,
                    address(this)
                )
            );
        }
        require(token.ownerOf(8) == address(this), "wrong owner rollback");

        try token.mint(address(0xbeef), 8) {
            revert("expected duplicate");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721InvalidSender.selector,
                    address(0)
                )
            );
        }
        require(token.ownerOf(8) == address(this), "duplicate rollback");

        token.burn(8);
        require(token.balanceOf(address(this)) == 0, "burn balance");
        try token.ownerOf(8) returns (address) {
            revert("expected burn nonexistent");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC721Errors.ERC721NonexistentToken.selector,
                    8
                )
            );
        }
    }
}
