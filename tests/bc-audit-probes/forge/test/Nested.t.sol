// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Nested} from "../src/Nested.sol";
contract NestedForgeTest {
    Nested private t = new Nested();
    function testU8Intermediate() public {
        try t.u8IntermediateOverflow() returns (uint8) { revert("no panic u8"); }
        catch Panic(uint256 c) { require(c == 0x11, "wrong u8 code"); }
    }
    function testU8MulChain() public {
        try t.u8MulChain() returns (uint8) { revert("no panic mul"); }
        catch Panic(uint256 c) { require(c == 0x11, "wrong mul code"); }
    }
    function testI8Intermediate() public {
        try t.i8IntermediateOverflow() returns (int8) { revert("no panic i8"); }
        catch Panic(uint256 c) { require(c == 0x11, "wrong i8 code"); }
    }
    function testU8UncheckedChain() public view {
        require(t.u8UncheckedChain() == 200, "unchecked chain val"); // (200+100)&255=44; 44-100=-56&255=200
    }
    function testU8UncheckedMul() public view {
        require(t.u8UncheckedMul() == 88, "unchecked mul val"); // (200+100)&255=44; 44*2=88
    }
}
