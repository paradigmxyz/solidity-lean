// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract TransientMix {
    uint256 p;              // persistent, slot 0
    uint256 transient t;    // transient, transient-slot 0
    function setBoth(uint256 pv, uint256 tv) external returns (uint256, uint256) {
        p = pv;
        t = tv;
        return (p, t);
    }
}
