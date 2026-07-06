// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DuplicateLowLevelValueOption {
    function bad(address payable target, bytes calldata payload)
        external
        returns (bool, bytes memory)
    {
        return target.call{value: 1, value: 2}(payload);
    }
}
