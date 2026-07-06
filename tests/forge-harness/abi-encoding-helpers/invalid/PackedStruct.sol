// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PackedStruct {
    struct Item {
        uint256 value;
    }

    function bad(Item memory item) external pure returns (bytes memory) {
        return abi.encodePacked(item);
    }
}
