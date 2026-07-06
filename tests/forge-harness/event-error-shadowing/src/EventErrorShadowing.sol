// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

error FileBad(uint256 value);
event FileHit(uint256 indexed value, uint256 amount);

contract UsesFreeEventError {
    function failFree(uint256 value) external pure {
        revert FileBad(value);
    }

    function emitFree(uint256 value) external {
        emit FileHit(value, value + 1);
    }

    function emitFreeNamed(uint256 value) external {
        emit FileHit({amount: value + 2, value: value});
    }
}

contract LocalShadow {
    error FileBad(address who);
    event FileHit(address indexed who, uint256 amount);

    function failLocal(address who) external pure {
        revert FileBad(who);
    }

    function emitLocal(address who, uint256 amount) external {
        emit FileHit(who, amount);
    }
}

contract InheritedBase {
    error Collision();
    event CollisionEvent();

    function failInherited() external pure {
        revert Collision();
    }

    function emitInherited() external {
        emit CollisionEvent();
    }
}

contract InheritedDerived is InheritedBase {}
