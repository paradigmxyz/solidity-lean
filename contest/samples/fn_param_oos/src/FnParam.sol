// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// X-FNARG (register 1.4, the narrow residue of the retired X-ARGVAL): a
// FUNCTION-typed ENTRY PARAMETER stays out of scope — no meaningful external
// function VALUE can be fabricated from a claim (no callee exists behind an
// arbitrary (address,selector) pair in the v1 responder-free world).
contract FnParam {
    function useCb(function() external pure returns (uint256) cb)
        external
        pure
        returns (uint256)
    {
        cb;
        return 1;
    }
}
