// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinERC1155CoreHarness,
    OpenZeppelinERC1155CoreSpender,
    OpenZeppelinIERC1155Core,
    OpenZeppelinIERC1155Errors,
    OpenZeppelinIERC1155MetadataURI
} from "../src/OpenZeppelinERC1155Core.sol";

contract OpenZeppelinERC1155CoreForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function _ids(uint256 first, uint256 second)
        private
        pure
        returns (uint256[] memory values)
    {
        values = new uint256[](2);
        values[0] = first;
        values[1] = second;
    }

    function _accounts(address first, address second)
        private
        pure
        returns (address[] memory values)
    {
        values = new address[](2);
        values[0] = first;
        values[1] = second;
    }

    function testMetadataInterfaceIdsAndUri() public {
        OpenZeppelinERC1155CoreHarness token =
            new OpenZeppelinERC1155CoreHarness();

        require(
            keccak256(bytes(token.uri(7))) ==
                keccak256(bytes("ipfs://token-cdn.example/{id}.json")),
            "uri"
        );
        require(
            token.supportsInterface(type(OpenZeppelinIERC1155Core).interfaceId),
            "core id"
        );
        require(
            token.supportsInterface(
                type(OpenZeppelinIERC1155MetadataURI).interfaceId
            ),
            "metadata id"
        );
        require(token.supportsInterface(0x01ffc9a7), "erc165 id");
        require(!token.supportsInterface(0xffffffff), "unknown id");

        token.setBaseURI("ipfs://updated/{id}.json");
        require(
            keccak256(bytes(token.uri(7))) ==
                keccak256(bytes("ipfs://updated/{id}.json")),
            "updated uri"
        );
    }

    function testMintTransferAndBurnSingle() public {
        OpenZeppelinERC1155CoreHarness token =
            new OpenZeppelinERC1155CoreHarness();

        token.mint(address(this), 7, 11);
        require(token.balanceOf(address(this), 7) == 11, "mint balance");

        token.safeTransferFrom(address(this), address(0xbeef), 7, 4, "");
        require(token.balanceOf(address(this), 7) == 7, "sender balance");
        require(token.balanceOf(address(0xbeef), 7) == 4, "receiver balance");

        token.burn(address(this), 7, 2);
        require(token.balanceOf(address(this), 7) == 5, "burn balance");
    }

    function testOperatorBatchTransferAndUnset() public {
        OpenZeppelinERC1155CoreHarness token =
            new OpenZeppelinERC1155CoreHarness();
        OpenZeppelinERC1155CoreSpender spender =
            new OpenZeppelinERC1155CoreSpender();

        uint256[] memory ids = _ids(1, 2);
        uint256[] memory values = _ids(10, 20);
        token.mintBatch(address(this), ids, values);
        token.setApprovalForAll(address(spender), true);
        require(
            token.isApprovedForAll(address(this), address(spender)),
            "operator approved"
        );

        uint256[] memory transferValues = _ids(3, 8);
        spender.batchTransferFromToken(
            token,
            address(this),
            address(0xcafe),
            ids,
            transferValues
        );
        require(token.balanceOf(address(this), 1) == 7, "owner token 1");
        require(token.balanceOf(address(this), 2) == 12, "owner token 2");
        require(token.balanceOf(address(0xcafe), 1) == 3, "recipient token 1");
        require(token.balanceOf(address(0xcafe), 2) == 8, "recipient token 2");

        token.setApprovalForAll(address(spender), false);
        require(
            !token.isApprovedForAll(address(this), address(spender)),
            "operator unset"
        );
    }

    function testBalanceOfBatchAndLengthError() public {
        OpenZeppelinERC1155CoreHarness token =
            new OpenZeppelinERC1155CoreHarness();

        token.mint(address(0xa11ce), 1, 4);
        token.mint(address(0xb0b), 2, 9);

        uint256[] memory balances =
            token.balanceOfBatch(_accounts(address(0xa11ce), address(0xb0b)), _ids(1, 2));
        require(balances.length == 2, "batch length");
        require(balances[0] == 4, "alice balance");
        require(balances[1] == 9, "bob balance");

        uint256[] memory oneId = new uint256[](1);
        oneId[0] = 1;
        try token.balanceOfBatch(_accounts(address(0xa11ce), address(0xb0b)), oneId)
            returns (uint256[] memory)
        {
            revert("expected length mismatch");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors
                        .ERC1155InvalidArrayLength
                        .selector,
                    1,
                    2
                )
            );
        }
    }

    function testErrorsAndRollback() public {
        OpenZeppelinERC1155CoreHarness token =
            new OpenZeppelinERC1155CoreHarness();

        try token.mint(address(0), 1, 5) {
            revert("expected invalid receiver");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors.ERC1155InvalidReceiver.selector,
                    address(0)
                )
            );
        }

        token.mint(address(0xa11ce), 1, 5);
        try token.safeTransferFrom(address(0xa11ce), address(0xbeef), 1, 1, "") {
            revert("expected missing approval");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors
                        .ERC1155MissingApprovalForAll
                        .selector,
                    address(this),
                    address(0xa11ce)
                )
            );
        }
        require(token.balanceOf(address(0xa11ce), 1) == 5, "approval rollback");

        token.mint(address(this), 2, 3);
        try token.safeTransferFrom(address(this), address(0), 2, 1, "") {
            revert("expected invalid receiver");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors.ERC1155InvalidReceiver.selector,
                    address(0)
                )
            );
        }
        require(token.balanceOf(address(this), 2) == 3, "receiver rollback");

        try token.burn(address(0xa11ce), 1, 8) {
            revert("expected insufficient balance");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors
                        .ERC1155InsufficientBalance
                        .selector,
                    address(0xa11ce),
                    5,
                    8,
                    1
                )
            );
        }
        require(token.balanceOf(address(0xa11ce), 1) == 5, "balance rollback");

        try token.setApprovalForAll(address(0), true) {
            revert("expected invalid operator");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC1155Errors.ERC1155InvalidOperator.selector,
                    address(0)
                )
            );
        }
    }
}
