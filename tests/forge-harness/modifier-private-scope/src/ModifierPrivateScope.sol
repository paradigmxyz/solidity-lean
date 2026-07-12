// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// #199 MODIFIER-BODY-PRIVATE-VAR-SCOPE: a base modifier reading a PRIVATE
/// state variable of its declaring contract, attached to functions declared
/// in derived contracts — the OZ Ownable/Pausable mixin pattern.
abstract contract Ownable2 {
    address private _owner;

    constructor() {
        _owner = msg.sender;
    }

    modifier onlyOwner() {
        require(msg.sender == _owner, "own");
        _;
    }

    function owner() public view returns (address) {
        return _owner;
    }
}

abstract contract Pausable2 is Ownable2 {
    bool private _paused;

    modifier whenNotPaused() {
        require(!_paused, "paused");
        _;
    }

    function pause() external onlyOwner {
        _paused = true;
    }

    function isPaused() public view returns (bool) {
        return _paused;
    }
}

abstract contract Guard2 {
    uint256 private _lock;

    modifier guarded() {
        require(_lock == 0, "lock");
        _lock = 1;
        _;
        _lock = 0;
    }
}

contract Vault2 is Pausable2, Guard2 {
    mapping(address => uint256) private _bal;

    function deposit(uint256 amt) external whenNotPaused guarded {
        _bal[msg.sender] += amt;
    }

    function balanceOf(address who) public view returns (uint256) {
        return _bal[who];
    }
}

/// Control: a derived PRIVATE variable with the same name as the base's does
/// NOT capture the base modifier's read — the modifier binds the BASE slot.
abstract contract ShadowBase {
    uint256 private _x;

    constructor() {
        _x = 7;
    }

    modifier gate() {
        require(_x == 7, "gate");
        _;
    }

    function baseX() public view returns (uint256) {
        return _x;
    }
}

contract ShadowDerived is ShadowBase {
    uint256 private _x;
    uint256 public n;

    constructor() {
        _x = 99;
    }

    function f() external gate {
        n = n + 1;
    }

    function derivedX() public view returns (uint256) {
        return _x;
    }
}

/// Control: an INTERNAL base variable read by the base modifier (worked
/// before the fix and must keep working).
abstract contract InternalOwned {
    address internal _keeper;

    constructor() {
        _keeper = msg.sender;
    }

    modifier onlyKeeper() {
        require(msg.sender == _keeper, "keep");
        _;
    }
}

contract InternalOwnedTarget is InternalOwned {
    uint256 public n;

    function f() external onlyKeeper {
        n = n + 1;
    }
}
