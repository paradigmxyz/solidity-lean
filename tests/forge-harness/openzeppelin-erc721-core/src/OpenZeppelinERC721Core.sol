// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined, assembly-free ERC721 core adaptation from OpenZeppelin
// Contracts v5.6.1. Safe-transfer receiver checks are intentionally omitted
// because the source-semantics harness keeps inline assembly/Yul out of scope.
interface OpenZeppelinERC721IERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface OpenZeppelinIERC721Core is OpenZeppelinERC721IERC165 {
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

interface OpenZeppelinIERC721MetadataCore is OpenZeppelinIERC721Core {
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function tokenURI(uint256 tokenId) external view returns (string memory);
}

interface OpenZeppelinIERC721Errors {
    error ERC721InvalidOwner(address owner);
    error ERC721NonexistentToken(uint256 tokenId);
    error ERC721IncorrectOwner(
        address sender,
        uint256 tokenId,
        address owner
    );
    error ERC721InvalidSender(address sender);
    error ERC721InvalidReceiver(address receiver);
    error ERC721InsufficientApproval(address operator, uint256 tokenId);
    error ERC721InvalidApprover(address approver);
    error ERC721InvalidOperator(address operator);
}

abstract contract OpenZeppelinERC721Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

abstract contract OpenZeppelinERC721ERC165 is OpenZeppelinERC721IERC165 {
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinERC721IERC165).interfaceId;
    }
}

abstract contract OpenZeppelinERC721Core is
    OpenZeppelinERC721Context,
    OpenZeppelinERC721ERC165,
    OpenZeppelinIERC721MetadataCore,
    OpenZeppelinIERC721Errors
{
    string private _name;
    string private _symbol;
    mapping(uint256 tokenId => address) private _owners;
    mapping(address owner => uint256) private _balances;
    mapping(uint256 tokenId => address) private _tokenApprovals;
    mapping(address owner => mapping(address operator => bool)) private
        _operatorApprovals;

    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override(OpenZeppelinERC721ERC165, OpenZeppelinERC721IERC165)
        returns (bool)
    {
        return
            interfaceId == type(OpenZeppelinIERC721Core).interfaceId ||
            interfaceId == type(OpenZeppelinIERC721MetadataCore).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function balanceOf(address owner) public view virtual returns (uint256) {
        if (owner == address(0)) {
            revert ERC721InvalidOwner(address(0));
        }
        return _balances[owner];
    }

    function ownerOf(uint256 tokenId) public view virtual returns (address) {
        return _requireOwned(tokenId);
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
        _requireOwned(tokenId);
        return "";
    }

    function approve(address to, uint256 tokenId) public virtual {
        address owner = _msgSender();
        address previousOwner = _requireOwned(tokenId);
        if (previousOwner != owner && !isApprovedForAll(previousOwner, owner)) {
            revert ERC721InvalidApprover(owner);
        }
        _tokenApprovals[tokenId] = to;
        emit Approval(previousOwner, to, tokenId);
    }

    function getApproved(uint256 tokenId)
        public
        view
        virtual
        returns (address)
    {
        _requireOwned(tokenId);
        return _getApproved(tokenId);
    }

    function setApprovalForAll(address operator, bool approved)
        public
        virtual
    {
        address owner = _msgSender();
        _setApprovalForAll(owner, operator, approved);
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
        if (to == address(0)) {
            revert ERC721InvalidReceiver(address(0));
        }
        address spender = _msgSender();
        address previousOwner = _ownerOf(tokenId);
        _checkAuthorized(previousOwner, spender, tokenId);
        if (previousOwner != from) {
            revert ERC721IncorrectOwner(from, tokenId, previousOwner);
        }
        _tokenApprovals[tokenId] = address(0);
        unchecked {
            _balances[previousOwner] -= 1;
            _balances[to] += 1;
        }
        _owners[tokenId] = to;
        emit Transfer(previousOwner, to, tokenId);
    }

    function _ownerOf(uint256 tokenId)
        internal
        view
        virtual
        returns (address)
    {
        return _owners[tokenId];
    }

    function _getApproved(uint256 tokenId)
        internal
        view
        virtual
        returns (address)
    {
        return _tokenApprovals[tokenId];
    }

    function _isAuthorized(
        address owner,
        address spender,
        uint256 tokenId
    ) internal view virtual returns (bool) {
        return
            spender != address(0) &&
            (owner == spender ||
                isApprovedForAll(owner, spender) ||
                _getApproved(tokenId) == spender);
    }

    function _checkAuthorized(
        address owner,
        address spender,
        uint256 tokenId
    ) internal view virtual {
        if (!_isAuthorized(owner, spender, tokenId)) {
            if (owner == address(0)) {
                revert ERC721NonexistentToken(tokenId);
            } else {
                revert ERC721InsufficientApproval(spender, tokenId);
            }
        }
    }

    function _update(address to, uint256 tokenId, address auth)
        internal
        virtual
        returns (address)
    {
        address from = _ownerOf(tokenId);

        if (auth != address(0)) {
            _checkAuthorized(from, auth, tokenId);
        }

        if (from != address(0)) {
            _approve(address(0), tokenId, address(0), false);
            unchecked {
                _balances[from] -= 1;
            }
        }

        if (to != address(0)) {
            unchecked {
                _balances[to] += 1;
            }
        }

        _owners[tokenId] = to;

        emit Transfer(from, to, tokenId);

        return from;
    }

    function _mint(address to, uint256 tokenId) internal {
        if (to == address(0)) {
            revert ERC721InvalidReceiver(address(0));
        }
        address previousOwner = _update(to, tokenId, address(0));
        if (previousOwner != address(0)) {
            revert ERC721InvalidSender(address(0));
        }
    }

    function _burn(uint256 tokenId) internal {
        address previousOwner = _update(address(0), tokenId, address(0));
        if (previousOwner == address(0)) {
            revert ERC721NonexistentToken(tokenId);
        }
    }

    function _transfer(address from, address to, uint256 tokenId) internal {
        if (to == address(0)) {
            revert ERC721InvalidReceiver(address(0));
        }
        address previousOwner = _update(to, tokenId, address(0));
        if (previousOwner == address(0)) {
            revert ERC721NonexistentToken(tokenId);
        } else if (previousOwner != from) {
            revert ERC721IncorrectOwner(from, tokenId, previousOwner);
        }
    }

    function _approve(address to, uint256 tokenId, address auth) internal {
        _approve(to, tokenId, auth, true);
    }

    function _approve(
        address to,
        uint256 tokenId,
        address auth,
        bool emitEvent
    ) internal virtual {
        address owner = _requireOwned(tokenId);

        if (
            auth != address(0) &&
            owner != auth &&
            !isApprovedForAll(owner, auth)
        ) {
            revert ERC721InvalidApprover(auth);
        }

        _tokenApprovals[tokenId] = to;

        if (emitEvent) {
            emit Approval(owner, to, tokenId);
        }
    }

    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual {
        if (operator == address(0)) {
            revert ERC721InvalidOperator(address(0));
        }
        _operatorApprovals[owner][operator] = approved;
        emit ApprovalForAll(owner, operator, approved);
    }

    function _requireOwned(uint256 tokenId)
        internal
        view
        returns (address)
    {
        address owner = _ownerOf(tokenId);
        if (owner == address(0)) {
            revert ERC721NonexistentToken(tokenId);
        }
        return owner;
    }
}

contract OpenZeppelinERC721CoreHarness is OpenZeppelinERC721Core {
    constructor() OpenZeppelinERC721Core("Harness NFT", "HNFT") {}

    function mint(address to, uint256 tokenId) external {
        _mint(to, tokenId);
    }

    function burn(uint256 tokenId) external {
        _burn(tokenId);
    }

    function exposedTransfer(address from, address to, uint256 tokenId)
        external
    {
        _transfer(from, to, tokenId);
    }
}

contract OpenZeppelinERC721CoreSpender {
    function transferFromToken(
        OpenZeppelinERC721CoreHarness token,
        address from,
        address to,
        uint256 tokenId
    ) external {
        token.transferFrom(from, to, tokenId);
    }
}
