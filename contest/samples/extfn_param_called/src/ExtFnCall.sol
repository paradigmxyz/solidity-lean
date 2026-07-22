// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// X-EXTCALL (register 1.6): supplying an external function VALUE as an entry
// parameter is in scope (X-FNARG retired), but CALLING it is an external call
// like any other — there is no callee behind the submitted (address, selector)
// pair in the v1 responder-free world. The gate's function-value-call arm must
// flag `cb()` -> REJECTED_OOS.
contract ExtFnCall {
    function useCb(function() external view returns (uint256) cb)
        external
        view
        returns (uint256)
    {
        return cb();
    }
}
