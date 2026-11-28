// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Outside the envelope: delegatecall. Expected: BLOCKED (delegatecall).
contract Delegatecall {
    address public impl;

    /// @custom:ensures impl == old(impl)
    function run(bytes calldata data) external returns (bytes memory) {
        (bool ok, bytes memory out) = impl.delegatecall(data);
        require(ok, "call");
        return out;
    }
}
