// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.4 (X-FNVAL retired): an EXTERNAL function VALUE in the return
// channel is comparable — the model's Value.externalFunction carries the same
// (address, selector) pair the EVM ABI left-packs into its 24-byte word, and
// both sides render the canonical f:<addr>:<sel> form.
contract ExtFnRet {
    function probe() external pure returns (uint256) {
        return 7;
    }

    function get()
        external
        view
        returns (function() external pure returns (uint256))
    {
        return this.probe;
    }
}
