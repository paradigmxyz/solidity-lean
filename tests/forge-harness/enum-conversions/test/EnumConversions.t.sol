// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EnumConversions} from "../src/EnumConversions.sol";

contract EnumConversionsForgeTest {
    EnumConversions private target = new EnumConversions();

    function testInRangeEnumConversions() public view {
        require(target.enumInRange() == 2, "Color(2)");
        require(target.enumZero() == 0, "Color(0)");
        require(target.enumMemberToUint() == 2, "uint8(Color.Blue)");
    }

    function testOutOfRangeEnumConversionPanics() public {
        try target.enumOutOfRange() returns (uint8) {
            revert("expected out-of-range enum panic");
        } catch Panic(uint256 code) {
            require(code == 0x21, "wrong enum conversion panic");
        }
    }
}
