// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/LibStoragePublic2.sol";

contract LibStoragePublic2ForgeTest {
    function testMappingValueStoragePointer() public {
        LibStoragePublic2 t = new LibStoragePublic2();

        // Mapping-value storage pointer: L2.pushPub(m[k], v).
        t.pushMapping(3, 11);
        require(t.mapLen(3) == 1, "mapLen after first push");
        require(t.mapElem(3, 0) == 11, "m[3][0]");

        t.pushMapping(3, 22);
        require(t.mapLen(3) == 2, "mapLen after second push");
        require(t.mapElem(3, 1) == 22, "m[3][1]");

        // A different key must be untouched (proves the keccak slot depends on k).
        require(t.mapLen(4) == 0, "m[4] untouched");

        // view library call reading the same mapping value.
        require(t.mapSum(3) == 33, "mapSum(3)");
    }

    function testStructMemberStoragePointer() public {
        LibStoragePublic2 t = new LibStoragePublic2();

        // Struct-member array storage pointer via using-for: s.a.pushPub(v).
        t.pushStruct(99);
        require(t.structLen() == 1, "structLen after push");
        require(t.structElem(0) == 99, "s.a[0]");

        t.pushStruct(100);
        require(t.structLen() == 2, "structLen after second push");
        require(t.structElem(1) == 100, "s.a[1]");
    }

    function testStoragePointerLocal() public {
        LibStoragePublic2 t = new LibStoragePublic2();

        t.addRow(); // aa now has one (empty) row at index 0
        t.addRow(); // aa now has a second row at index 1

        // Storage-pointer local bound to a nested-array element:
        //   uint256[] storage p = aa[0]; L2.pushPub(p, v);
        t.pushLocal(0, 77);
        require(t.aaLen(0) == 1, "aa[0].length");
        require(t.aaElem(0, 0) == 77, "aa[0][0]");

        // Row 1 must be untouched (proves the slot depends on i).
        require(t.aaLen(1) == 0, "aa[1] untouched");

        t.pushLocal(1, 88);
        require(t.aaLen(1) == 1, "aa[1].length");
        require(t.aaElem(1, 0) == 88, "aa[1][0]");
    }
}
