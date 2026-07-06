// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DuplicateLowLevelGasOption {
    function bad(address target, bytes calldata payload)
        external
        returns (bool, bytes memory)
    {
        return target.call{gas: 1, gas: 2}(payload);
    }
}
