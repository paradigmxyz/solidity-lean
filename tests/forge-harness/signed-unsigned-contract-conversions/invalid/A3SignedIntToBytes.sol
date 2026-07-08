// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A3 (reverse direction): IntegerType::isExplicitlyConvertibleTo to FixedBytes
// (Types.cpp:638-639) requires !isSigned(). int256 -> bytes32 is rejected.
// Pinned solc 0.8.35 rejects: "Explicit type conversion not allowed from
// \"int256\" to \"bytes32\"."
contract A3SignedIntToBytes {
    function f(int256 x) public pure returns (bytes32) {
        return bytes32(x);
    }
}
