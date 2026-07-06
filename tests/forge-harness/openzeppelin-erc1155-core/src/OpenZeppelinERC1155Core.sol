// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

// Import-inlined, assembly-free ERC1155 core adaptation from OpenZeppelin
// Contracts v5.6.1. Contract receiver acceptance hooks are intentionally
// omitted because the source-semantics harness keeps inline assembly/Yul and
// bytecode-level receiver inspection out of scope.
interface OpenZeppelinERC1155IERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface OpenZeppelinIERC1155Core is OpenZeppelinERC1155IERC165 {
    event TransferSingle(
        address indexed operator,
        address indexed from,
        address indexed to,
        uint256 id,
        uint256 value
    );
    event TransferBatch(
        address indexed operator,
        address indexed from,
        address indexed to,
        uint256[] ids,
        uint256[] values
    );
    event ApprovalForAll(
        address indexed account,
        address indexed operator,
        bool approved
    );
    event URI(string value, uint256 indexed id);

    function balanceOf(address account, uint256 id)
        external
        view
        returns (uint256);
    function balanceOfBatch(address[] memory accounts, uint256[] memory ids)
        external
        view
        returns (uint256[] memory);
    function setApprovalForAll(address operator, bool approved) external;
    function isApprovedForAll(address account, address operator)
        external
        view
        returns (bool);
    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 value,
        bytes memory data
    ) external;
    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory values,
        bytes memory data
    ) external;
}

interface OpenZeppelinIERC1155MetadataURI is OpenZeppelinIERC1155Core {
    function uri(uint256 id) external view returns (string memory);
}

interface OpenZeppelinIERC1155Errors {
    error ERC1155InsufficientBalance(
        address sender,
        uint256 balance,
        uint256 needed,
        uint256 tokenId
    );
    error ERC1155InvalidSender(address sender);
    error ERC1155InvalidReceiver(address receiver);
    error ERC1155MissingApprovalForAll(address operator, address owner);
    error ERC1155InvalidApprover(address approver);
    error ERC1155InvalidOperator(address operator);
    error ERC1155InvalidArrayLength(uint256 idsLength, uint256 valuesLength);
}

abstract contract OpenZeppelinERC1155Context {
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

abstract contract OpenZeppelinERC1155ERC165 is OpenZeppelinERC1155IERC165 {
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinERC1155IERC165).interfaceId;
    }
}

abstract contract OpenZeppelinERC1155Core is
    OpenZeppelinERC1155Context,
    OpenZeppelinERC1155ERC165,
    OpenZeppelinIERC1155MetadataURI,
    OpenZeppelinIERC1155Errors
{
    mapping(uint256 id => mapping(address account => uint256)) private
        _balances;
    mapping(address account => mapping(address operator => bool)) private
        _operatorApprovals;
    string private _uri;

    constructor(string memory uri_) {
        _setURI(uri_);
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override(OpenZeppelinERC1155ERC165, OpenZeppelinERC1155IERC165)
        returns (bool)
    {
        return
            interfaceId == type(OpenZeppelinIERC1155Core).interfaceId ||
            interfaceId == type(OpenZeppelinIERC1155MetadataURI).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function uri(uint256) public view virtual returns (string memory) {
        return _uri;
    }

    function balanceOf(address account, uint256 id)
        public
        view
        virtual
        returns (uint256)
    {
        return _balances[id][account];
    }

    function balanceOfBatch(address[] memory accounts, uint256[] memory ids)
        public
        view
        virtual
        returns (uint256[] memory)
    {
        if (accounts.length != ids.length) {
            revert ERC1155InvalidArrayLength(ids.length, accounts.length);
        }

        uint256[] memory batchBalances = new uint256[](accounts.length);
        for (uint256 i = 0; i < accounts.length; ++i) {
            batchBalances[i] = balanceOf(accounts[i], ids[i]);
        }
        return batchBalances;
    }

    function setApprovalForAll(address operator, bool approved)
        public
        virtual
    {
        _setApprovalForAll(_msgSender(), operator, approved);
    }

    function isApprovedForAll(address account, address operator)
        public
        view
        virtual
        returns (bool)
    {
        return _operatorApprovals[account][operator];
    }

    function safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 value,
        bytes memory data
    ) public virtual {
        data;
        _checkAuthorized(_msgSender(), from);
        _safeTransferFrom(from, to, id, value);
    }

    function safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory values,
        bytes memory data
    ) public virtual {
        data;
        _checkAuthorized(_msgSender(), from);
        _safeBatchTransferFrom(from, to, ids, values);
    }

    function _checkAuthorized(address operator, address owner)
        internal
        view
        virtual
    {
        if (owner != operator && !isApprovedForAll(owner, operator)) {
            revert ERC1155MissingApprovalForAll(operator, owner);
        }
    }

    function _update(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory values
    ) internal virtual {
        if (ids.length != values.length) {
            revert ERC1155InvalidArrayLength(ids.length, values.length);
        }

        address operator = _msgSender();
        for (uint256 i = 0; i < ids.length; ++i) {
            uint256 id = ids[i];
            uint256 value = values[i];

            if (from != address(0)) {
                uint256 fromBalance = _balances[id][from];
                if (fromBalance < value) {
                    revert ERC1155InsufficientBalance(
                        from,
                        fromBalance,
                        value,
                        id
                    );
                }
                unchecked {
                    _balances[id][from] = fromBalance - value;
                }
            }

            if (to != address(0)) {
                _balances[id][to] += value;
            }
        }

        if (ids.length == 1) {
            emit TransferSingle(operator, from, to, ids[0], values[0]);
        } else {
            emit TransferBatch(operator, from, to, ids, values);
        }
    }

    function _safeTransferFrom(
        address from,
        address to,
        uint256 id,
        uint256 value
    ) internal {
        if (to == address(0)) {
            revert ERC1155InvalidReceiver(address(0));
        }
        if (from == address(0)) {
            revert ERC1155InvalidSender(address(0));
        }
        (uint256[] memory ids, uint256[] memory values) =
            _asSingletonArrays(id, value);
        _update(from, to, ids, values);
    }

    function _safeBatchTransferFrom(
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory values
    ) internal {
        if (to == address(0)) {
            revert ERC1155InvalidReceiver(address(0));
        }
        if (from == address(0)) {
            revert ERC1155InvalidSender(address(0));
        }
        _update(from, to, ids, values);
    }

    function _setURI(string memory newuri) internal virtual {
        _uri = newuri;
    }

    function _mint(address to, uint256 id, uint256 value) internal {
        if (to == address(0)) {
            revert ERC1155InvalidReceiver(address(0));
        }
        (uint256[] memory ids, uint256[] memory values) =
            _asSingletonArrays(id, value);
        _update(address(0), to, ids, values);
    }

    function _mintBatch(
        address to,
        uint256[] memory ids,
        uint256[] memory values
    ) internal {
        if (to == address(0)) {
            revert ERC1155InvalidReceiver(address(0));
        }
        _update(address(0), to, ids, values);
    }

    function _burn(address from, uint256 id, uint256 value) internal {
        if (from == address(0)) {
            revert ERC1155InvalidSender(address(0));
        }
        (uint256[] memory ids, uint256[] memory values) =
            _asSingletonArrays(id, value);
        _update(from, address(0), ids, values);
    }

    function _burnBatch(
        address from,
        uint256[] memory ids,
        uint256[] memory values
    ) internal {
        if (from == address(0)) {
            revert ERC1155InvalidSender(address(0));
        }
        _update(from, address(0), ids, values);
    }

    function _setApprovalForAll(
        address owner,
        address operator,
        bool approved
    ) internal virtual {
        if (owner == address(0)) {
            revert ERC1155InvalidApprover(address(0));
        }
        if (operator == address(0)) {
            revert ERC1155InvalidOperator(address(0));
        }
        _operatorApprovals[owner][operator] = approved;
        emit ApprovalForAll(owner, operator, approved);
    }

    function _asSingletonArrays(uint256 element1, uint256 element2)
        private
        pure
        returns (uint256[] memory array1, uint256[] memory array2)
    {
        array1 = new uint256[](1);
        array2 = new uint256[](1);
        array1[0] = element1;
        array2[0] = element2;
    }
}

contract OpenZeppelinERC1155CoreHarness is OpenZeppelinERC1155Core {
    constructor()
        OpenZeppelinERC1155Core("ipfs://token-cdn.example/{id}.json")
    {}

    function mint(address to, uint256 id, uint256 value) external {
        _mint(to, id, value);
    }

    function mintBatch(
        address to,
        uint256[] memory ids,
        uint256[] memory values
    ) external {
        _mintBatch(to, ids, values);
    }

    function burn(address from, uint256 id, uint256 value) external {
        _burn(from, id, value);
    }

    function burnBatch(
        address from,
        uint256[] memory ids,
        uint256[] memory values
    ) external {
        _burnBatch(from, ids, values);
    }

    function setBaseURI(string memory newuri) external {
        _setURI(newuri);
    }
}

contract OpenZeppelinERC1155CoreSpender {
    function transferFromToken(
        OpenZeppelinERC1155CoreHarness token,
        address from,
        address to,
        uint256 id,
        uint256 value
    ) external {
        token.safeTransferFrom(from, to, id, value, "");
    }

    function batchTransferFromToken(
        OpenZeppelinERC1155CoreHarness token,
        address from,
        address to,
        uint256[] memory ids,
        uint256[] memory values
    ) external {
        token.safeBatchTransferFrom(from, to, ids, values, "");
    }
}
