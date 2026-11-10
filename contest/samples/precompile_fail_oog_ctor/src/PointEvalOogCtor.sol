// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// The constructor-frame form of precompile_fail_oog: the CREATE runs out of
// gas on the EVM, the model deploys.
contract PointEvalOogCtor {
    uint256 public n;

    constructor() {
        for (uint256 i = 0; i < 13; i++) {
            (bool ok, ) = address(10).staticcall(abi.encode(bytes32(0), bytes32(0)));
            if (!ok) n++;
        }
    }

    function get() external view returns (uint256) {
        return n;
    }
}
