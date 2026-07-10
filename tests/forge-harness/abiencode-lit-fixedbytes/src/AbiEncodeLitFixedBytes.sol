// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #140 ABIENCODE-LIT-FIXEDBYTES: a string / hex / bytes LITERAL passed to a
// fixed `bytesN` parameter over a call or `new C(...)` boundary must be
// ABI-encoded by solc as ONE left-aligned 32-byte word (NOT the dynamic
// head/length/data of `bytes`/`string`). A literal targeting a DYNAMIC
// `bytes`/`string` parameter must stay dynamic.

contract AbiLitC {
    bytes2 public s;

    constructor(bytes2 b) {
        s = b;
    }

    function f(bytes2 b) external pure returns (bytes2) {
        return b;
    }
}

contract AbiLitE {
    bytes32 public s;

    constructor(bytes32 b) {
        s = b;
    }
}

contract AbiLitDynC {
    bytes public s;

    constructor(bytes memory b) {
        s = b;
    }
}

contract AbiLitFactory {
    // `new C(hex"1234")` — hex literal to a bytes2 constructor parameter.
    function makeCtorHex() external returns (AbiLitC) {
        return new AbiLitC(hex"1234");
    }

    // `new C("ab")` — string literal to a bytes2 constructor parameter.
    function makeCtorStr() external returns (AbiLitC) {
        return new AbiLitC("ab");
    }

    // `new E(hex"deadbeef")` — hex literal to a bytes32 constructor parameter.
    function makeCtorBig() external returns (AbiLitE) {
        return new AbiLitE(hex"deadbeef");
    }

    // `new C(hex"1234")` to a DYNAMIC `bytes` parameter — stays dynamic.
    function makeDyn() external returns (AbiLitDynC) {
        return new AbiLitDynC(hex"1234");
    }

    // External member call `c.f(hex"abcd")` — hex literal to a bytes2 parameter.
    function callF(AbiLitC c) external view returns (bytes2) {
        return c.f(hex"abcd");
    }
}
