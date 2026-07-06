// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of selected paths from
// OpenZeppelin Contracts v4.9.6 ERC721URIStorage, ERC721, IERC4906, and ERC165.
// Safe-transfer receiver bytecode checks and the upstream Strings.toString
// assembly helper used by the base-only tokenURI fallback are intentionally
// omitted at this Solidity source layer.
interface OpenZeppelinURIStorageIERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface OpenZeppelinURIStorageIERC4906 is OpenZeppelinURIStorageIERC165 {
    event MetadataUpdate(uint256 indexed tokenId);
    event BatchMetadataUpdate(uint256 indexed fromTokenId, uint256 indexed toTokenId);
}

interface OpenZeppelinURIStorageIERC721 is OpenZeppelinURIStorageIERC165 {
    event Transfer(
        address indexed from,
        address indexed to,
        uint256 indexed tokenId
    );
    event Approval(
        address indexed owner,
        address indexed approved,
        uint256 indexed tokenId
    );
    event ApprovalForAll(
        address indexed owner,
        address indexed operator,
        bool approved
    );

    function balanceOf(address owner) external view returns (uint256);
    function ownerOf(uint256 tokenId) external view returns (address);
    function approve(address to, uint256 tokenId) external;
    function getApproved(uint256 tokenId) external view returns (address);
    function setApprovalForAll(address operator, bool approved) external;
    function isApprovedForAll(address owner, address operator)
        external
        view
        returns (bool);
    function transferFrom(address from, address to, uint256 tokenId) external;
}

interface OpenZeppelinURIStorageIERC721Metadata is
    OpenZeppelinURIStorageIERC721
{
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function tokenURI(uint256 tokenId) external view returns (string memory);
}

abstract contract OpenZeppelinURIStorageContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

abstract contract OpenZeppelinURIStorageERC165 is OpenZeppelinURIStorageIERC165 {
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinURIStorageIERC165).interfaceId;
    }
}

contract OpenZeppelinURIStorageERC721 is
    OpenZeppelinURIStorageContext,
    OpenZeppelinURIStorageERC165
{
    string private _name;
    string private _symbol;

    mapping(uint256 => address) private _owners;
    mapping(address => uint256) private _balances;
    mapping(uint256 => address) private _tokenApprovals;
    mapping(address => mapping(address => bool)) private _operatorApprovals;

    event Transfer(
        address indexed from,
        address indexed to,
        uint256 indexed tokenId
    );
    event Approval(
        address indexed owner,
        address indexed approved,
        uint256 indexed tokenId
    );
    event ApprovalForAll(
        address indexed owner,
        address indexed operator,
        bool approved
    );

    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override
        returns (bool)
    {
        return
            interfaceId == type(OpenZeppelinURIStorageIERC721).interfaceId ||
            interfaceId == type(OpenZeppelinURIStorageIERC721Metadata).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function balanceOf(address owner) public view virtual returns (uint256) {
        require(owner != address(0), "ERC721: address zero is not a valid owner");
        return _balances[owner];
    }

    function ownerOf(uint256 tokenId) public view virtual returns (address) {
        address owner = _ownerOf(tokenId);
        require(owner != address(0), "ERC721: invalid token ID");
        return owner;
    }

    function name() public view virtual returns (string memory) {
        return _name;
    }

    function symbol() public view virtual returns (string memory) {
        return _symbol;
    }

    function tokenURI(uint256 tokenId)
        public
        view
        virtual
        returns (string memory)
    {
        ownerOf(tokenId);
        return "";
    }

    function approve(address to, uint256 tokenId) public virtual {
        address owner = ownerOf(tokenId);
        require(to != owner, "ERC721: approval to current owner");

        address sender = _msgSender();
        require(
            sender == owner || isApprovedForAll(owner, sender),
            "ERC721: approve caller is not token owner or approved for all"
        );

        _approve(to, tokenId);
    }

    function getApproved(uint256 tokenId)
        public
        view
        virtual
        returns (address)
    {
        require(_exists(tokenId), "ERC721: invalid token ID");
        return _tokenApprovals[tokenId];
    }

    function setApprovalForAll(address operator, bool approved)
        public
        virtual
    {
        _setApprovalForAll(_msgSender(), operator, approved);
    }

    function isApprovedForAll(address owner, address operator)
        public
        view
        virtual
        returns (bool)
    {
        return _operatorApprovals[owner][operator];
    }

    function transferFrom(address from, address to, uint256 tokenId)
        public
        virtual
    {
        address sender = _msgSender();
        require(
            _isApprovedOrOwner(sender, tokenId),
            "ERC721: caller is not token owner or approved"
        );
        _transfer(from, to, tokenId);
    }

    function _ownerOf(uint256 tokenId)
        internal
        view
        virtual
        returns (address)
    {
        return _owners[tokenId];
    }

    function _exists(uint256 tokenId) internal view virtual returns (bool) {
        return _ownerOf(tokenId) != address(0);
    }

    function _requireMinted(uint256 tokenId) internal view virtual {
        require(_exists(tokenId), "ERC721: invalid token ID");
    }

    function _isApprovedOrOwner(address spender, uint256 tokenId)
        internal
        view
        virtual
        returns (bool)
    {
        address owner = ownerOf(tokenId);
        return
            spender == owner ||
            isApprovedForAll(owner, spender) ||
            getApproved(tokenId) == spender;
    }

    function _mint(address to, uint256 tokenId) internal virtual {
        require(to != address(0), "ERC721: mint to the zero address");
        require(!_exists(tokenId), "ERC721: token already minted");

        _beforeTokenTransfer(address(0), to, tokenId, 1);

        unchecked {
            _balances[to] += 1;
        }
        _owners[tokenId] = to;

        emit Transfer(address(0), to, tokenId);

        _afterTokenTransfer(address(0), to, tokenId, 1);
    }

    function _burn(uint256 tokenId) internal virtual {
        address owner = ownerOf(tokenId);

        _beforeTokenTransfer(owner, address(0), tokenId, 1);

        _approve(address(0), tokenId);

        unchecked {
            _balances[owner] -= 1;
        }
        delete _owners[tokenId];

        emit Transfer(owner, address(0), tokenId);

        _afterTokenTransfer(owner, address(0), tokenId, 1);
    }

    function _transfer(address from, address to, uint256 tokenId)
        internal
        virtual
    {
        require(
            ownerOf(tokenId) == from,
            "ERC721: transfer from incorrect owner"
        );
        require(to != address(0), "ERC721: transfer to the zero address");

        _beforeTokenTransfer(from, to, tokenId, 1);

        require(
            ownerOf(tokenId) == from,
            "ERC721: transfer from incorrect owner"
        );

        _approve(address(0), tokenId);

        unchecked {
            _balances[from] -= 1;
            _balances[to] += 1;
        }
        _owners[tokenId] = to;

        emit Transfer(from, to, tokenId);

        _afterTokenTransfer(from, to, tokenId, 1);
    }

    function _approve(address to, uint256 tokenId) internal virtual {
        _tokenApprovals[tokenId] = to;
        address owner = ownerOf(tokenId);
        emit Approval(owner, to, tokenId);
    }

    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual {
        require(owner != operator, "ERC721: approve to caller");
        _operatorApprovals[owner][operator] = approved;
        emit ApprovalForAll(owner, operator, approved);
    }

    function _baseURI() internal view virtual returns (string memory) {
        return "";
    }

    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 tokenId,
        uint256 batchSize
    ) internal virtual {}

    function _afterTokenTransfer(
        address from,
        address to,
        uint256 tokenId,
        uint256 batchSize
    ) internal virtual {}
}

abstract contract OpenZeppelinERC721URIStorage is
    OpenZeppelinURIStorageIERC4906,
    OpenZeppelinURIStorageERC721
{
    mapping(uint256 => string) private _tokenURIs;

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override(OpenZeppelinURIStorageIERC165, OpenZeppelinURIStorageERC721)
        returns (bool)
    {
        return interfaceId == 0x49064906 || super.supportsInterface(interfaceId);
    }

    function tokenURI(uint256 tokenId)
        public
        view
        virtual
        override
        returns (string memory)
    {
        _requireMinted(tokenId);

        string memory storedTokenURI = _tokenURIs[tokenId];
        string memory base = _baseURI();

        if (bytes(base).length == 0) {
            return storedTokenURI;
        }

        if (bytes(storedTokenURI).length > 0) {
            return string(abi.encodePacked(base, storedTokenURI));
        }

        return super.tokenURI(tokenId);
    }

    function _setTokenURI(uint256 tokenId, string memory storedTokenURI)
        internal
        virtual
    {
        require(_exists(tokenId), "ERC721URIStorage: URI set of nonexistent token");
        _tokenURIs[tokenId] = storedTokenURI;

        emit MetadataUpdate(tokenId);
    }

    function _burn(uint256 tokenId)
        internal
        virtual
        override(OpenZeppelinURIStorageERC721)
    {
        super._burn(tokenId);

        delete _tokenURIs[tokenId];
    }
}

contract OpenZeppelinERC721URIStorageHarness is OpenZeppelinERC721URIStorage {
    string private _base;

    constructor() OpenZeppelinURIStorageERC721("URI Storage NFT", "URIS") {}

    function mint(address to, uint256 tokenId) external {
        _mint(to, tokenId);
    }

    function burn(uint256 tokenId) external {
        address sender = _msgSender();
        require(
            _isApprovedOrOwner(sender, tokenId),
            "ERC721: caller is not token owner or approved"
        );
        _burn(tokenId);
    }

    function setTokenURI(uint256 tokenId, string memory storedTokenURI)
        external
    {
        _setTokenURI(tokenId, storedTokenURI);
    }

    function setBaseURI(string memory base) external {
        _base = base;
    }

    function batchMetadataUpdate(uint256 fromTokenId, uint256 toTokenId)
        external
    {
        emit BatchMetadataUpdate(fromTokenId, toTokenId);
    }

    function _baseURI() internal view override returns (string memory) {
        return _base;
    }
}
