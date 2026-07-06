// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-inlined adaptation of OpenZeppelin Contracts v4.9.6
// `Context.sol`, `security/Pausable.sol`, and
// `security/ReentrancyGuard.sol`.
abstract contract OpenZeppelinSecurityContext {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

abstract contract OpenZeppelinPausable is OpenZeppelinSecurityContext {
    event Paused(address account);
    event Unpaused(address account);

    bool private _paused;

    constructor() {
        _paused = false;
    }

    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    modifier whenPaused() {
        _requirePaused();
        _;
    }

    function paused() public view virtual returns (bool) {
        return _paused;
    }

    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}

abstract contract OpenZeppelinReentrancyGuard {
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        _status = _NOT_ENTERED;
    }

    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

contract OpenZeppelinPausableReentrancyHarness is
    OpenZeppelinPausable,
    OpenZeppelinReentrancyGuard
{
    uint256 public touches;
    uint256 public enteredTouches;

    function touch() external whenNotPaused nonReentrant returns (uint256) {
        touches += 1;
        return touches;
    }

    function pausedTouch() external whenPaused returns (uint256) {
        touches += 10;
        return touches;
    }

    function pause() external {
        _pause();
    }

    function unpause() external {
        _unpause();
    }

    function entered() external view returns (bool) {
        return _reentrancyGuardEntered();
    }

    function probeEnteredDuringGuard()
        external
        nonReentrant
        returns (bool)
    {
        bool duringGuard = _reentrancyGuardEntered();
        if (duringGuard) {
            enteredTouches += 1;
        }
        return duringGuard;
    }

    function failInsideGuard() external nonReentrant {
        touches += 100;
        revert("boom");
    }

    function callOtherNonReentrant()
        external
        nonReentrant
        returns (uint256)
    {
        return this.touch();
    }
}
