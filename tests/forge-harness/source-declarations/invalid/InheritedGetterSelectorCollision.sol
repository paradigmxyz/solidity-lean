// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract GetterSelectorCollisionBase {
    mapping(uint256 => uint256) public burn;
}

contract InheritedGetterSelectorCollision is GetterSelectorCollisionBase {
    function collate_propagate_storage(bytes16 value)
        external
        pure
        returns (bytes16)
    {
        return value;
    }
}
