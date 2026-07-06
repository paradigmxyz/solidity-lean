// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined ERC6909 core adaptation from OpenZeppelin Contracts v5.6.1.
interface OpenZeppelinERC6909IERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface OpenZeppelinIERC6909 is OpenZeppelinERC6909IERC165 {
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 indexed id,
        uint256 amount
    );

    event OperatorSet(
        address indexed owner,
        address indexed spender,
        bool approved
    );

    event Transfer(
        address caller,
        address indexed sender,
        address indexed receiver,
        uint256 indexed id,
        uint256 amount
    );

    function balanceOf(address owner, uint256 id)
        external
        view
        returns (uint256);
    function allowance(address owner, address spender, uint256 id)
        external
        view
        returns (uint256);
    function isOperator(address owner, address spender)
        external
        view
        returns (bool);
    function approve(address spender, uint256 id, uint256 amount)
        external
        returns (bool);
    function setOperator(address spender, bool approved)
        external
        returns (bool);
    function transfer(address receiver, uint256 id, uint256 amount)
        external
        returns (bool);
    function transferFrom(
        address sender,
        address receiver,
        uint256 id,
        uint256 amount
    ) external returns (bool);
}

abstract contract OpenZeppelinERC6909Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
}

abstract contract OpenZeppelinERC6909ERC165 is OpenZeppelinERC6909IERC165 {
    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        returns (bool)
    {
        return interfaceId == type(OpenZeppelinERC6909IERC165).interfaceId;
    }
}

contract OpenZeppelinERC6909Core is
    OpenZeppelinERC6909Context,
    OpenZeppelinERC6909ERC165,
    OpenZeppelinIERC6909
{
    mapping(address owner => mapping(uint256 id => uint256)) private _balances;
    mapping(address owner => mapping(address operator => bool)) private
        _operatorApprovals;
    mapping(address owner => mapping(address spender => mapping(uint256 id => uint256)))
        private _allowances;

    error ERC6909InsufficientBalance(
        address sender,
        uint256 balance,
        uint256 needed,
        uint256 id
    );
    error ERC6909InsufficientAllowance(
        address spender,
        uint256 allowance,
        uint256 needed,
        uint256 id
    );
    error ERC6909InvalidApprover(address approver);
    error ERC6909InvalidReceiver(address receiver);
    error ERC6909InvalidSender(address sender);
    error ERC6909InvalidSpender(address spender);

    function supportsInterface(bytes4 interfaceId)
        public
        view
        virtual
        override(OpenZeppelinERC6909ERC165, OpenZeppelinERC6909IERC165)
        returns (bool)
    {
        return
            interfaceId == type(OpenZeppelinIERC6909).interfaceId ||
            super.supportsInterface(interfaceId);
    }

    function balanceOf(address owner, uint256 id)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _balances[owner][id];
    }

    function allowance(address owner, address spender, uint256 id)
        public
        view
        virtual
        override
        returns (uint256)
    {
        return _allowances[owner][spender][id];
    }

    function isOperator(address owner, address spender)
        public
        view
        virtual
        override
        returns (bool)
    {
        return _operatorApprovals[owner][spender];
    }

    function approve(address spender, uint256 id, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _approve(_msgSender(), spender, id, amount);
        return true;
    }

    function setOperator(address spender, bool approved)
        public
        virtual
        override
        returns (bool)
    {
        _setOperator(_msgSender(), spender, approved);
        return true;
    }

    function transfer(address receiver, uint256 id, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _transfer(_msgSender(), receiver, id, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address receiver,
        uint256 id,
        uint256 amount
    ) public virtual override returns (bool) {
        address caller = _msgSender();
        if (sender != caller && !isOperator(sender, caller)) {
            _spendAllowance(sender, caller, id, amount);
        }
        _transfer(sender, receiver, id, amount);
        return true;
    }

    function _mint(address to, uint256 id, uint256 amount) internal {
        if (to == address(0)) {
            revert ERC6909InvalidReceiver(address(0));
        }
        _update(address(0), to, id, amount);
    }

    function _transfer(
        address from,
        address to,
        uint256 id,
        uint256 amount
    ) internal {
        if (from == address(0)) {
            revert ERC6909InvalidSender(address(0));
        }
        if (to == address(0)) {
            revert ERC6909InvalidReceiver(address(0));
        }
        _update(from, to, id, amount);
    }

    function _burn(address from, uint256 id, uint256 amount) internal {
        if (from == address(0)) {
            revert ERC6909InvalidSender(address(0));
        }
        _update(from, address(0), id, amount);
    }

    function _update(
        address from,
        address to,
        uint256 id,
        uint256 amount
    ) internal virtual {
        address caller = _msgSender();

        if (from != address(0)) {
            uint256 fromBalance = _balances[from][id];
            if (fromBalance < amount) {
                revert ERC6909InsufficientBalance(
                    from,
                    fromBalance,
                    amount,
                    id
                );
            }
            unchecked {
                _balances[from][id] = fromBalance - amount;
            }
        }
        if (to != address(0)) {
            _balances[to][id] += amount;
        }

        emit Transfer(caller, from, to, id, amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 id,
        uint256 amount
    ) internal virtual {
        if (owner == address(0)) {
            revert ERC6909InvalidApprover(address(0));
        }
        if (spender == address(0)) {
            revert ERC6909InvalidSpender(address(0));
        }
        _allowances[owner][spender][id] = amount;
        emit Approval(owner, spender, id, amount);
    }

    function _setOperator(address owner, address spender, bool approved)
        internal
        virtual
    {
        if (owner == address(0)) {
            revert ERC6909InvalidApprover(address(0));
        }
        if (spender == address(0)) {
            revert ERC6909InvalidSpender(address(0));
        }
        _operatorApprovals[owner][spender] = approved;
        emit OperatorSet(owner, spender, approved);
    }

    function _spendAllowance(
        address owner,
        address spender,
        uint256 id,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender, id);
        if (currentAllowance < type(uint256).max) {
            if (currentAllowance < amount) {
                revert ERC6909InsufficientAllowance(
                    spender,
                    currentAllowance,
                    amount,
                    id
                );
            }
            unchecked {
                _allowances[owner][spender][id] = currentAllowance - amount;
            }
        }
    }
}

contract OpenZeppelinERC6909CoreHarness is OpenZeppelinERC6909Core {
    function mint(address to, uint256 id, uint256 amount) external {
        _mint(to, id, amount);
    }

    function burn(address from, uint256 id, uint256 amount) external {
        _burn(from, id, amount);
    }
}

contract OpenZeppelinERC6909CoreSpender {
    function transferFromToken(
        OpenZeppelinERC6909CoreHarness token,
        address sender,
        address receiver,
        uint256 id,
        uint256 amount
    ) external returns (bool) {
        return token.transferFrom(sender, receiver, id, amount);
    }
}
