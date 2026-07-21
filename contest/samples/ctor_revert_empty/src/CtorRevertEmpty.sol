// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Constructor-revert lane: bare revert() in the constructor -> zero-length
// revert data. Both engines must render deployrevert|empty.
contract CtorRevertEmpty {
    uint256 public v;

    constructor() {
        revert();
    }

    function get() external view returns (uint256) {
        return v;
    }
}
