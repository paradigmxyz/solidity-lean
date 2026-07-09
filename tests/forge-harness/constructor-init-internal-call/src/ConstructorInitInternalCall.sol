// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CTOR-RESIDUE gap (b): inline state-variable initializer that calls an
// internal function.
//
// solc runs inline state-variable initializers as part of the constructor with
// full expression support, so an initializer such as `uint256 y = setY();` or
// `uint256 z = double(y);` is legal and runs before the constructor body.
// Initializers run in declaration order, whole hierarchy base->derived, ahead
// of every constructor body:
//   y = setY()      => 7
//   z = double(y)   => double(7) == 14
//   (constructor)   w = y + z == 21
//
// The pre-fix lowering ran state-variable initializers through the plain
// expression lowering, which has no internal-call machinery, so any initializer
// containing an internal call failed to lower (over-reject). The fix routes
// initializers through the same internal-call-capable statement lowering the
// constructor body uses, while preserving the legacy inits-before-bodies order.

contract ConstructorInitInternalCall {
    uint256 public y = setY();
    uint256 public z = double(y);
    uint256 public w;

    constructor() {
        w = y + z;
    }

    function setY() internal pure returns (uint256) {
        return 7;
    }

    function double(uint256 v) internal pure returns (uint256) {
        return v * 2;
    }
}
