// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Adapted from OpenZeppelin Contracts v5.6.1 Context and Ownable, with imports
// inlined because the source-semantics harness intentionally excludes import
// resolution.
abstract contract OpenZeppelinContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
}

abstract contract OpenZeppelinOwnable is OpenZeppelinContext {
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

    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
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

contract OpenZeppelinOwnableHarnessTarget is OpenZeppelinOwnable {
    uint256 private _touches;

    constructor(address initialOwner) OpenZeppelinOwnable(initialOwner) {}

    function guardedTouch() external onlyOwner returns (uint256) {
        _touches += 1;
        return _touches;
    }

    function touches() external view returns (uint256) {
        return _touches;
    }
}

contract OpenZeppelinOwnableForwarder {
    function guardedTouch(OpenZeppelinOwnableHarnessTarget target)
        external
        returns (uint256)
    {
        return target.guardedTouch();
    }

    function renounce(OpenZeppelinOwnableHarnessTarget target)
        external
        returns (address)
    {
        target.renounceOwnership();
        return target.owner();
    }
}
