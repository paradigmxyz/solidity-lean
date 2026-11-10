// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// SEM-CLOSEDGAS without a named gas quantity: each failing point-evaluation
// staticcall burns all the gas forwarded to it, so the loop runs the entry
// frame out of gas on the EVM. The model does not meter gas.
contract PointEvalOog {
    function f() external view returns (uint256 n) {
        for (uint256 i = 0; i < 13; i++) {
            (bool ok, ) = address(10).staticcall(abi.encode(bytes32(0), bytes32(0)));
            if (!ok) n++;
        }
    }
}
