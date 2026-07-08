// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// PK1 guard: solc REJECTS packed encoding of an array whose *base* (element) is
// itself a dynamically-sized array (error 9578, "Type not supported in packed
// mode"). uint8[][3] has a dynamic inner dimension -> reject.
contract PackedDynamicInnerArray {
    function bad(uint8[][3] memory grid) external pure returns (bytes memory) {
        return abi.encodePacked(grid);
    }
}
