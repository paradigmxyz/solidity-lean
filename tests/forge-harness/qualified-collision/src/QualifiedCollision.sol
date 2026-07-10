// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

library L {
    event Ev(uint8 x);
    error E(uint8 x);
}

library N {
    event Ping(uint64 p);
    error Bad(uint64 b);
}

contract QualifiedCollisionTarget {
    // Same NAMES as library L's members, but DIFFERENT signatures — the
    // collision that used to mis-target the by-name runtime table (#136/#137).
    event Ev(uint256 x);
    error E(uint256 x);

    // Library-qualified emit/revert under a name collision: solc encodes L's
    // member (Ev(uint8) topic0 / E(uint8) selector), NOT the contract's.
    function emitLib() external {
        emit L.Ev(5);
    }

    function revertLib() external {
        revert L.E(5);
    }

    // The contract's own (bare) event/error — must stay unchanged.
    function emitOwn() external {
        emit Ev(9);
    }

    function revertOwn() external {
        revert E(9);
    }

    // Library-qualified with NO contract-level collision: used to be
    // over-rejected (event) / already worked (error). Both must be accepted.
    function emitLibNoCollision() external {
        emit N.Ping(3);
    }

    function revertLibNoCollision() external {
        revert N.Bad(3);
    }
}
