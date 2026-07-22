// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// NEGATIVE control (fabrication fence, register 1.4): a fixed `uint256[3]`
// parameter fed only 2 elements is not a legal call — the two engines would
// receive different logical calls. Must be REJECT_MALFORMED, never a gap.
contract FixArrBad {
    function total(uint256[3] memory xs) external pure returns (uint256) {
        return xs[0] + xs[1] + xs[2];
    }
}
