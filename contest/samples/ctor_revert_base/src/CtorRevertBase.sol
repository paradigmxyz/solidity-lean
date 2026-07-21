// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Constructor-revert lane: the FAILING BASE constructor. Derived's own body is
// empty; the inherited Base(0) constructor call fails its require. Both engines
// must render deployrevert|error:base zero.
contract Base {
    uint256 public b;

    constructor(uint256 x) {
        require(x != 0, "base zero");
        b = x;
    }
}

contract CtorRevertBase is Base(0) {
    function get() external view returns (uint256) {
        return b;
    }
}
