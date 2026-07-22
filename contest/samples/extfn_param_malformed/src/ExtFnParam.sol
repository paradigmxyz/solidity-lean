// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.6 (X-FNARG retired): an EXTERNAL function-typed ENTRY PARAMETER
// is encodable end-to-end — the claim arg is a 2-element [address, selector]
// list, the EVM receives the 24-byte left-packed ABI word
// (addr << 96) | (sel << 64) and the model receives Value.externalFunction
// with the SAME pair. The entry only INSPECTS the value (.address/.selector);
// CALLING it would be X-EXTCALL.
contract ExtFnParam {
    function inspect(function() external view returns (uint256) f)
        external
        pure
        returns (address, bytes4)
    {
        return (f.address, f.selector);
    }
}
