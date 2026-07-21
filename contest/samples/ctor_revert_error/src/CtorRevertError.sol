// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Constructor-revert lane: deployed with x=42, the constructor's require fails
// with Error("ctor bad"). The deploy itself reverts — both engines must render
// deployrevert|error:ctor bad (the entry call never runs).
contract CtorRevertError {
    uint256 public v;

    constructor(uint256 x) {
        require(x < 10, "ctor bad");
        v = x;
    }

    function get() external view returns (uint256) {
        return v;
    }
}
