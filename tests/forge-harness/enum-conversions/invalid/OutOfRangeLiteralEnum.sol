// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

enum Color { Red, Green, Blue }

// solc rejects an out-of-range *raw* literal enum conversion at compile time:
// "Explicit type conversion not allowed from int_const 3 to enum Color."
// (A runtime out-of-range value instead reverts with Panic(0x21) — see
// EnumConversions.enumOutOfRange.)
contract OutOfRangeLiteralEnum {
    function bad() external pure returns (uint8) {
        Color c = Color(3);
        return uint8(c);
    }
}
