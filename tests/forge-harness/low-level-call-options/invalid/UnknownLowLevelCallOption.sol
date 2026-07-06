// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract UnknownLowLevelCallOption {
    function bad(address target, bytes calldata payload)
        external
        returns (bool, bytes memory)
    {
        return target.call{foo: 1}(payload);
    }
}
