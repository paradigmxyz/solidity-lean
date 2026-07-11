// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {AddressFoldedConstTarget} from "../src/AddressFoldedConst.sol";

contract AddressFoldedConstForgeTest {
    function testAddCast() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.addCast() == address(2), "addCast");
    }
    function testMulCast() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.mulCast() == address(6), "mulCast");
    }
    function testHexAddCast() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.hexAddCast() == address(0x1235), "hexAddCast");
    }
    function testSubZeroCast() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.subZeroCast() == address(0), "subZeroCast");
    }
    function testMaxCast() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.maxCast() == address(type(uint160).max), "maxCast");
    }
    function testPlainLit() public {
        AddressFoldedConstTarget t = new AddressFoldedConstTarget();
        require(t.plainLit() == address(2), "plainLit");
    }
}
