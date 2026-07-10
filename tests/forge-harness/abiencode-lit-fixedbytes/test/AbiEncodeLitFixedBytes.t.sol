// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    AbiLitC,
    AbiLitE,
    AbiLitDynC,
    AbiLitFactory
} from "../src/AbiEncodeLitFixedBytes.sol";

contract AbiEncodeLitFixedBytesForgeTest {
    AbiLitFactory internal factory;

    function setUp() public {
        factory = new AbiLitFactory();
    }

    // hex literal -> bytes2 constructor param encodes as a single left-aligned
    // word; C's constructor reads it back as 0x1234.
    function testCtorHex() public {
        AbiLitC c = factory.makeCtorHex();
        require(c.s() == bytes2(hex"1234"), "ctor hex");
    }

    // string literal -> bytes2 constructor param.
    function testCtorStr() public {
        AbiLitC c = factory.makeCtorStr();
        require(c.s() == bytes2(0x6162), "ctor str");
    }

    // hex literal -> bytes32 constructor param.
    function testCtorBig() public {
        AbiLitE e = factory.makeCtorBig();
        require(
            e.s() == bytes32(hex"deadbeef"),
            "ctor big"
        );
    }

    // hex literal -> DYNAMIC bytes constructor param stays dynamic.
    function testDyn() public {
        AbiLitDynC d = factory.makeDyn();
        require(keccak256(d.s()) == keccak256(hex"1234"), "dyn");
    }

    // hex literal -> bytes2 external call param.
    function testCallF() public {
        AbiLitC c = new AbiLitC(hex"0000");
        require(factory.callF(c) == bytes2(hex"abcd"), "call f");
    }
}
