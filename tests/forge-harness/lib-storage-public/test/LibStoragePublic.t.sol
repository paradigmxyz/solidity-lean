// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/LibStoragePublic.sol";

contract LibStoragePublicForgeTest {
    function testStoragePointerPublicLibrary() public {
        LibStoragePublic target = new LibStoragePublic();

        // using-for delegatecall: arr.pushPub(5)
        target.viaUsing(5);
        require(target.len() == 1, "len after viaUsing");
        require(target.elem(0) == 5, "arr[0] after viaUsing");

        // direct delegatecall: L.pushPub(arr, 7)
        target.viaDirect(7);
        require(target.len() == 2, "len after viaDirect");
        require(target.elem(1) == 7, "arr[1] after viaDirect");

        // view delegatecall reading storage: arr.sumPub()
        require(target.total() == 12, "total after pushes");
    }
}
