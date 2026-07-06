// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Adapted from OpenZeppelin Contracts v5.6.1 VestingWallet, Context,
// Ownable, Address, and SafeERC20, with imports inlined because the
// source-semantics harness intentionally excludes import resolution. The
// helper libraries are kept assembly-free because inline assembly/Yul is out
// of scope for this Solidity source layer.
abstract contract OpenZeppelinVestingContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
}

abstract contract OpenZeppelinVestingOwnable is OpenZeppelinVestingContext {
    address private _owner;

    error OwnableUnauthorizedAccount(address account);
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    function owner() public view virtual returns (address) {
        return _owner;
    }

    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

interface OpenZeppelinVestingIERC20 {
    function balanceOf(address account) external view returns (uint256);

    function transfer(address to, uint256 value) external returns (bool);
}

library OpenZeppelinVestingAddress {
    error InsufficientBalance(uint256 balance, uint256 needed);
    error FailedCall();

    function sendValue(address payable recipient, uint256 amount) internal {
        if (address(this).balance < amount) {
            revert InsufficientBalance(address(this).balance, amount);
        }

        (bool success, ) = recipient.call{value: amount}("");
        if (!success) {
            revert FailedCall();
        }
    }
}

library OpenZeppelinVestingSafeERC20 {
    error SafeERC20FailedOperation(address token);

    function safeTransfer(
        OpenZeppelinVestingIERC20 token,
        address to,
        uint256 value
    ) internal {
        if (!token.transfer(to, value)) {
            revert SafeERC20FailedOperation(address(token));
        }
    }
}

contract OpenZeppelinVestingWallet is
    OpenZeppelinVestingContext,
    OpenZeppelinVestingOwnable
{
    event EtherReleased(uint256 amount);
    event ERC20Released(address indexed token, uint256 amount);

    uint256 private _released;
    mapping(address token => uint256) private _erc20Released;

    uint64 private immutable _start;
    uint64 private immutable _duration;

    constructor(
        address beneficiary,
        uint64 startTimestamp,
        uint64 durationSeconds
    ) payable OpenZeppelinVestingOwnable(beneficiary) {
        _start = startTimestamp;
        _duration = durationSeconds;
    }

    receive() external payable virtual {}

    function start() public view virtual returns (uint256) {
        return _start;
    }

    function duration() public view virtual returns (uint256) {
        return _duration;
    }

    function end() public view virtual returns (uint256) {
        return start() + duration();
    }

    function released() public view virtual returns (uint256) {
        return _released;
    }

    function released(address token) public view virtual returns (uint256) {
        return _erc20Released[token];
    }

    function releasable() public view virtual returns (uint256) {
        uint256 vested = vestedAmount(uint64(block.timestamp));
        uint256 alreadyReleased = released();
        return vested - alreadyReleased;
    }

    function releasable(address token) public view virtual returns (uint256) {
        uint256 vested = vestedAmount(token, uint64(block.timestamp));
        uint256 alreadyReleased = released(token);
        return vested - alreadyReleased;
    }

    function release() public virtual {
        uint256 amount = releasable();
        _released += amount;
        emit EtherReleased(amount);
        address currentOwner = owner();
        OpenZeppelinVestingAddress.sendValue(payable(currentOwner), amount);
    }

    function release(address token) public virtual {
        uint256 amount = releasable(token);
        _erc20Released[token] += amount;
        emit ERC20Released(token, amount);
        address currentOwner = owner();
        OpenZeppelinVestingSafeERC20.safeTransfer(
            OpenZeppelinVestingIERC20(token),
            currentOwner,
            amount
        );
    }

    function vestedAmount(uint64 timestamp)
        public
        view
        virtual
        returns (uint256)
    {
        uint256 alreadyReleased = released();
        uint256 totalAllocation = address(this).balance + alreadyReleased;
        return _vestingSchedule(totalAllocation, timestamp);
    }

    function vestedAmount(address token, uint64 timestamp)
        public
        view
        virtual
        returns (uint256)
    {
        uint256 currentBalance =
            OpenZeppelinVestingIERC20(token).balanceOf(address(this));
        uint256 alreadyReleased = released(token);
        uint256 totalAllocation = currentBalance + alreadyReleased;
        return _vestingSchedule(totalAllocation, timestamp);
    }

    function _vestingSchedule(uint256 totalAllocation, uint64 timestamp)
        internal
        view
        virtual
        returns (uint256)
    {
        uint256 startTimestamp = start();
        if (timestamp < startTimestamp) {
            return 0;
        }

        uint256 durationSeconds = duration();
        uint256 endTimestamp = startTimestamp + durationSeconds;
        if (timestamp >= endTimestamp) {
            return totalAllocation;
        }

        uint256 elapsed = timestamp - startTimestamp;
        return (totalAllocation * elapsed) / durationSeconds;
    }
}

contract OpenZeppelinVestingMockToken {
    mapping(address account => uint256) public balanceOf;
    bool public failTransfer;

    function mint(address account, uint256 value) external {
        balanceOf[account] += value;
    }

    function setFailTransfer(bool fail) external {
        failTransfer = fail;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        if (failTransfer) {
            return false;
        }
        require(balanceOf[msg.sender] >= value);
        balanceOf[msg.sender] -= value;
        balanceOf[to] += value;
        return true;
    }
}

contract OpenZeppelinVestingRejectEther {
    receive() external payable {
        revert("reject");
    }
}
