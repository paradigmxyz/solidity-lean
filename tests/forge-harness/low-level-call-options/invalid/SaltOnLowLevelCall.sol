// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract SaltOnLowLevelCall {
    function run(address target, bytes calldata payload)
        external
        returns (bool, bytes memory)
    {
        return target.call{salt: bytes32(0)}(payload);
    }
}
