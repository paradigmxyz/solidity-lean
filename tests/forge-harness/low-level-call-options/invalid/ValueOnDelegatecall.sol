// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ValueOnDelegatecall {
    function run(address target, bytes calldata payload)
        external
        returns (bool, bytes memory)
    {
        return target.delegatecall{value: 1}(payload);
    }
}
