// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract SelectorCollisionBase {
    function burn(uint256 value) external pure returns (uint256) {
        return value;
    }
}

contract InheritedFunctionSelectorCollision is SelectorCollisionBase {
    function collate_propagate_storage(bytes16 value)
        external
        pure
        returns (bytes16)
    {
        return value;
    }
}
