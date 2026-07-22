// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// X-INTFNARG (register 1.6, the narrow residue of the retired X-FNARG —
// external function-typed parameters are now encoded end-to-end): a scalar
// parameter family whose legal domain the v1 claim arg forms cannot bound
// from the type string alone (here bytesN with N < 32) stays out of scope —
// an unvalidated leaf would let a submitter feed the two engines different
// logical calls and fabricate a divergence.
contract FnParam {
    function useB(bytes4 b) external pure returns (uint256) {
        b;
        return 1;
    }
}
