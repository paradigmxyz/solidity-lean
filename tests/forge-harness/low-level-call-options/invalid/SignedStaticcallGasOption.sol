// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract SignedStaticcallGasOption {
    function run(address target, bytes calldata payload, int256 gasAmount)
        external
        view
        returns (bool, bytes memory)
    {
        return target.staticcall{gas: gasAmount}(payload);
    }
}
