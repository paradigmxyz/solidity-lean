// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc validates the elements of a `memory`-location aggregate parameter
// EAGERLY at decode: the argument is copied out of calldata element-by-element
// through each element's `<validator>`, reverting `revert(0,0)` immediately on
// a dirty narrow-int element even if that element is never read. A `calldata`
// aggregate keeps the reference in calldata and validates each element LAZILY
// on access, so reading `.length` (or a clean sibling) of a calldata argument
// with a dirty element succeeds. These paired functions expose both behaviors.
contract AbiMemoryEager {
    struct NarrowPair {
        uint8 first;
        uint8 second;
    }

    // Memory aggregate: element cleanup is eager (dirty unused element reverts).
    function memArrayLength(uint8[] memory input) external pure returns (uint256) {
        return input.length;
    }

    function memPairFirst(NarrowPair memory input) external pure returns (uint8) {
        return input.first;
    }

    // Calldata aggregate: element cleanup is lazy (dirty unused element ok).
    function cdArrayLength(uint8[] calldata input) external pure returns (uint256) {
        return input.length;
    }

    function cdPairFirst(NarrowPair calldata input) external pure returns (uint8) {
        return input.first;
    }
}
