// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExpNarrowBaseWideExpTarget} from "../src/ExpNarrowBaseWideExp.sol";

contract ExpNarrowBaseWideExpForgeTest {
    function testBaseNoOverflow() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        require(t.g(2, 7) == 128, "g27");
    }
    function testBaseOverflowPanics() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("g(uint8,uint16)", 2, 8));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testBaseOverflowPanicsTen() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("g(uint8,uint16)", 2, 10));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testCastOverflowPanics() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("h(uint8,uint16)", 2, 8));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testMirrorNoPanic() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        require(t.mirror(2, 8) == 256, "mirror256");
    }
    function testWideBaseValue() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        require(t.wideBase(2, 200) == (2 ** 200), "wide2p200");
    }
    function testSignedBaseValue() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        require(t.sgn(-2, 7) == -128, "sgnMin");
    }
    function testSignedBaseOverflowPanics() public {
        ExpNarrowBaseWideExpTarget t = new ExpNarrowBaseWideExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("sgn(int8,uint16)", 2, 7));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
}
