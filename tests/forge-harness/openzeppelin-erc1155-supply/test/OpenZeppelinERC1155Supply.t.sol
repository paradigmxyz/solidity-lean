// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinERC1155SupplyHarness,
    OpenZeppelinERC1155SupplyIERC1155,
    OpenZeppelinERC1155SupplyIERC1155Errors,
    OpenZeppelinERC1155SupplyIERC1155MetadataURI,
    OpenZeppelinERC1155SupplySpender
} from "../src/OpenZeppelinERC1155Supply.sol";

contract OpenZeppelinERC1155SupplyForgeTest {
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

    function testMetadataInterfacesAndInitialSupply() public {
        OpenZeppelinERC1155SupplyHarness token =
            new OpenZeppelinERC1155SupplyHarness();

        require(
            keccak256(bytes(token.uri(7))) ==
                keccak256(bytes("ipfs://supply.example/{id}.json")),
            "uri"
        );
        require(
            token.supportsInterface(
                type(OpenZeppelinERC1155SupplyIERC1155).interfaceId
            ),
            "core id"
        );
        require(
            token.supportsInterface(
                type(OpenZeppelinERC1155SupplyIERC1155MetadataURI).interfaceId
            ),
            "metadata id"
        );
        require(token.supportsInterface(0x01ffc9a7), "erc165 id");
        require(!token.supportsInterface(0xffffffff), "unknown id");
        require(token.totalSupply() == 0, "all supply");
        require(token.totalSupply(7) == 0, "id supply");
        require(!token.exists(7), "exists");
    }

    function testMintBatchTransferAndBurnSupply() public {
        OpenZeppelinERC1155SupplyHarness token =
            new OpenZeppelinERC1155SupplyHarness();
        OpenZeppelinERC1155SupplySpender spender =
            new OpenZeppelinERC1155SupplySpender();
        ERC1155SupplyApprovalActor actor = new ERC1155SupplyApprovalActor();
        address alice = address(actor);
        address bob = address(0xb0b);

        token.mintBatch(alice, _ids(1, 2), _ids(10, 20));
        require(token.totalSupply(1) == 10, "supply 1");
        require(token.totalSupply(2) == 20, "supply 2");
        require(token.totalSupply() == 30, "supply all");
        require(token.exists(1) && token.exists(2), "exists");

        actor.setApproval(token, address(spender));
        spender.batchTransferFromToken(token, alice, bob, _ids(1, 2), _ids(3, 8));
        require(token.balanceOf(alice, 1) == 7, "alice 1");
        require(token.balanceOf(alice, 2) == 12, "alice 2");
        require(token.balanceOf(bob, 1) == 3, "bob 1");
        require(token.balanceOf(bob, 2) == 8, "bob 2");
        require(token.totalSupply(1) == 10, "transfer supply 1");
        require(token.totalSupply(2) == 20, "transfer supply 2");
        require(token.totalSupply() == 30, "transfer all");

        token.burn(alice, 1, 7);
        require(token.totalSupply(1) == 3, "burn supply 1");
        require(token.totalSupply() == 23, "burn all");
        require(token.exists(1), "exists after partial burn");

        token.burn(bob, 1, 3);
        require(token.totalSupply(1) == 0, "burn supply empty");
        require(!token.exists(1), "not exists");
        require(token.totalSupply() == 20, "final all");
    }

    function testBatchBurnAndRollback() public {
        OpenZeppelinERC1155SupplyHarness token =
            new OpenZeppelinERC1155SupplyHarness();
        address alice = address(0xa11ce);

        token.mintBatch(alice, _ids(1, 2), _ids(10, 20));

        uint256[] memory shortValues = new uint256[](1);
        shortValues[0] = 5;
        try token.mintBatch(alice, _ids(3, 4), shortValues) {
            revert("expected length mismatch");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC1155SupplyIERC1155Errors
                        .ERC1155InvalidArrayLength
                        .selector,
                    2,
                    1
                )
            );
        }
        require(token.totalSupply() == 30, "mint rollback all");
        require(token.totalSupply(3) == 0, "mint rollback id");

        try token.burn(alice, 1, 99) {
            revert("expected insufficient balance");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC1155SupplyIERC1155Errors
                        .ERC1155InsufficientBalance
                        .selector,
                    alice,
                    10,
                    99,
                    1
                )
            );
        }
        require(token.totalSupply(1) == 10, "burn rollback id");
        require(token.totalSupply() == 30, "burn rollback all");

        token.burnBatch(alice, _ids(1, 2), _ids(4, 5));
        require(token.totalSupply(1) == 6, "batch burn 1");
        require(token.totalSupply(2) == 15, "batch burn 2");
        require(token.totalSupply() == 21, "batch burn all");
    }

}

contract ERC1155SupplyApprovalActor {
    function setApproval(
        OpenZeppelinERC1155SupplyHarness token,
        address spender
    ) external {
        token.setApprovalForAll(spender, true);
    }
}
