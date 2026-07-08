// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Bare-literal cast probes: an integer literal or a *typed* conversion of a
// literal is cast to a narrower / differently-signed type. solc constant-folds
// each, applying the same mod-arithmetic and sign-extension a runtime cast
// would.  (An out-of-range *raw* literal such as `uint8(300)` is rejected by
// solc and lives in invalid/OutOfRangeLiteralCast.sol.)
contract LiteralCastConversions {
    // in-range raw literal: uint8(200) == 200
    function u8Literal200() external pure returns (uint8) {
        return uint8(200);
    }
    // uint8(uint256(0x1234)) truncates low byte -> 0x34 == 52
    function u8FromU256() external pure returns (uint8) {
        return uint8(uint256(0x1234));
    }
    // int8(uint8(200)): high bit set -> -56
    function i8FromU8_200() external pure returns (int8) {
        return int8(uint8(200));
    }
    // uint8(int8(-1)) reinterprets -> 255
    function u8FromI8Neg1() external pure returns (uint8) {
        return uint8(int8(-1));
    }
    // int16(int8(-1)) sign-extends -> -1
    function i16FromI8Neg1() external pure returns (int16) {
        return int16(int8(-1));
    }
    // uint256(int256(-1)) reinterprets -> 2**256 - 1
    function u256FromI256Neg1() external pure returns (uint256) {
        return uint256(int256(-1));
    }
}
