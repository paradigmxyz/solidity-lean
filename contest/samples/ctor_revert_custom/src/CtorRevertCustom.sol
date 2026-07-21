// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Constructor-revert lane: the constructor reverts with a CUSTOM error carrying
// a scalar arg. Both engines must render deployrevert|custom:CtorBad:w:42.
contract CtorRevertCustom {
    error CtorBad(uint256 got);

    uint256 public v;

    constructor(uint256 x) {
        if (x > 9) {
            revert CtorBad(x);
        }
        v = x;
    }

    function get() external view returns (uint256) {
        return v;
    }
}
