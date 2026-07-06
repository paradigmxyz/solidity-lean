// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinERC721URIStorageHarness,
    OpenZeppelinURIStorageIERC165,
    OpenZeppelinURIStorageIERC4906,
    OpenZeppelinURIStorageIERC721,
    OpenZeppelinURIStorageIERC721Metadata
} from "../src/OpenZeppelinERC721URIStorage.sol";

contract OpenZeppelinERC721URIStorageForgeTest {
    event MetadataUpdate(uint256 indexed tokenId);
    event BatchMetadataUpdate(uint256 indexed fromTokenId, uint256 indexed toTokenId);

    function _eq(string memory left, string memory right)
        private
        pure
        returns (bool)
    {
        return keccak256(bytes(left)) == keccak256(bytes(right));
    }

    function testMetadataInterfacesAndStoredURI() public {
        OpenZeppelinERC721URIStorageHarness token =
            new OpenZeppelinERC721URIStorageHarness();

        require(_eq(token.name(), "URI Storage NFT"), "name");
        require(_eq(token.symbol(), "URIS"), "symbol");
        require(token.supportsInterface(type(OpenZeppelinURIStorageIERC165).interfaceId), "erc165 id");
        require(token.supportsInterface(type(OpenZeppelinURIStorageIERC721).interfaceId), "erc721 id");
        require(
            token.supportsInterface(
                type(OpenZeppelinURIStorageIERC721Metadata).interfaceId
            ),
            "metadata id"
        );
        require(token.supportsInterface(0x49064906), "4906 id");
        require(!token.supportsInterface(0xffffffff), "unknown id");

        token.mint(address(this), 7);
        require(_eq(token.tokenURI(7), ""), "empty token uri");

        vmExpectMetadata(7);
        token.setTokenURI(7, "seven.json");
        require(_eq(token.tokenURI(7), "seven.json"), "stored token uri");
    }

    function testBaseURIConcatenationAndTransfer() public {
        OpenZeppelinERC721URIStorageHarness token =
            new OpenZeppelinERC721URIStorageHarness();
        OpenZeppelinERC721URIStorageActor actor =
            new OpenZeppelinERC721URIStorageActor();

        token.setBaseURI("ipfs://collection/");
        token.mint(address(this), 7);
        token.setTokenURI(7, "seven.json");
        require(
            _eq(token.tokenURI(7), "ipfs://collection/seven.json"),
            "joined uri"
        );

        token.approve(address(actor), 7);
        actor.transferToken(token, address(this), address(0xb0b), 7);
        require(token.ownerOf(7) == address(0xb0b), "owner");
        require(
            _eq(token.tokenURI(7), "ipfs://collection/seven.json"),
            "transfer keeps uri"
        );
        try token.getApproved(7) returns (address approved) {
            require(approved == address(0), "approval cleared");
        } catch {
            revert("approval lookup failed");
        }
    }

    function testBurnClearsStoredURIAndApproval() public {
        OpenZeppelinERC721URIStorageHarness token =
            new OpenZeppelinERC721URIStorageHarness();
        OpenZeppelinERC721URIStorageActor actor =
            new OpenZeppelinERC721URIStorageActor();

        token.setBaseURI("ipfs://collection/");
        token.mint(address(this), 7);
        token.setTokenURI(7, "seven.json");
        token.approve(address(actor), 7);
        actor.burnToken(token, 7);

        try token.tokenURI(7) returns (string memory) {
            revert("expected burned uri");
        } catch Error(string memory reason) {
            require(
                _eq(reason, "ERC721: invalid token ID"),
                "uri reason"
            );
        }

        try token.ownerOf(7) returns (address) {
            revert("expected burned owner");
        } catch Error(string memory reason) {
            require(_eq(reason, "ERC721: invalid token ID"), "owner reason");
        }

        token.mint(address(this), 7);
        require(_eq(token.tokenURI(7), ""), "uri deleted");
    }

    function testInvalidURISetAndMetadataEventsRollback() public {
        OpenZeppelinERC721URIStorageHarness token =
            new OpenZeppelinERC721URIStorageHarness();

        try token.setTokenURI(99, "missing.json") {
            revert("expected missing");
        } catch Error(string memory reason) {
            require(
                _eq(reason, "ERC721URIStorage: URI set of nonexistent token"),
                "missing reason"
            );
        }

        token.mint(address(this), 1);
        vmExpectMetadata(1);
        token.setTokenURI(1, "one.json");
        require(_eq(token.tokenURI(1), "one.json"), "one uri");

        token.setBaseURI("ipfs://base/");
        require(_eq(token.tokenURI(1), "ipfs://base/one.json"), "base one");

        vmExpectBatchMetadata(1, 3);
        token.batchMetadataUpdate(1, 3);
    }

    function vmExpectMetadata(uint256 tokenId) private {
        Vm vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
        vm.expectEmit(true, false, false, false);
        emit MetadataUpdate(tokenId);
    }

    function vmExpectBatchMetadata(uint256 fromTokenId, uint256 toTokenId)
        private
    {
        Vm vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
        vm.expectEmit(true, true, false, false);
        emit BatchMetadataUpdate(fromTokenId, toTokenId);
    }
}

contract OpenZeppelinERC721URIStorageActor {
    function transferToken(
        OpenZeppelinERC721URIStorageHarness token,
        address from,
        address to,
        uint256 tokenId
    ) external {
        token.transferFrom(from, to, tokenId);
    }

    function burnToken(OpenZeppelinERC721URIStorageHarness token, uint256 tokenId)
        external
    {
        token.burn(tokenId);
    }
}

interface Vm {
    function expectEmit(
        bool checkTopic1,
        bool checkTopic2,
        bool checkTopic3,
        bool checkData
    ) external;
}
