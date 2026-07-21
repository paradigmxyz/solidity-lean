// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Constructor-revert lane: the NO-ARG constructor hits a checked-arithmetic
// underflow -> Panic(0x11). Exercises the no-constructor-args deploy path with
// a reverting constructor. Both engines must render deployrevert|panic:17.
contract CtorRevertPanic {
    uint256 public v;

    constructor() {
        uint256 a = 0;
        v = a - 1; // checked underflow -> Panic(0x11)
    }

    function get() external view returns (uint256) {
        return v;
    }
}
