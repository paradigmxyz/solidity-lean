// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// NEGATIVE control (fabrication fence, register 1.4): a struct member value
// outside its leaf type's domain (uint8 = 300) is not a legal high-level call
// (the EVM ABI decoder would revert). Must be REJECT_MALFORMED, never a gap.
contract StructBad {
    struct Q {
        uint256 a;
        uint8 b;
    }

    function join(Q memory q) external pure returns (uint256) {
        return q.a + q.b;
    }
}
