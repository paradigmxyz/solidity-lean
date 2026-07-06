// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ValueOnStaticcall {
    function run(address target, bytes calldata payload)
        external
        view
        returns (bool, bytes memory)
    {
        return target.staticcall{value: 1}(payload);
    }
}
