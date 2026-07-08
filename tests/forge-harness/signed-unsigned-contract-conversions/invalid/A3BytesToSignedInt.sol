// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A3: FixedBytesType::isExplicitlyConvertibleTo (Types.cpp:1364-1365) allows
// bytesN -> integer only for UNSIGNED integers of the same bit width. bytes32
// -> int256 is rejected.
// Pinned solc 0.8.35 rejects: "Explicit type conversion not allowed from
// \"bytes32\" to \"int256\"."
contract A3BytesToSignedInt {
    function f(bytes32 x) public pure returns (int256) {
        return int256(x);
    }
}
