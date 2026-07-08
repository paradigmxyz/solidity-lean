// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LiteralCastConversions} from "../src/LiteralCastConversions.sol";

contract LiteralCastConversionsForgeTest {
    LiteralCastConversions private target = new LiteralCastConversions();

    function testInRangeLiteralCast() public view {
        require(target.u8Literal200() == 200, "uint8(200)");
    }

    function testTruncatingLiteralCasts() public view {
        require(target.u8FromU256() == 52, "uint8(uint256(0x1234))");
        require(target.i8FromU8_200() == -56, "int8(uint8(200))");
    }

    function testReinterpretingLiteralCasts() public view {
        require(target.u8FromI8Neg1() == 255, "uint8(int8(-1))");
        require(target.i16FromI8Neg1() == -1, "int16(int8(-1))");
        require(
            target.u256FromI256Neg1() == type(uint256).max,
            "uint256(int256(-1))"
        );
    }
}
