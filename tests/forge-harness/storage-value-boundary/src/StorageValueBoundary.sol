// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// R3 #192: builtins that need a value's BYTES (keccak256/sha256/erc7201,
/// abi.encode*/encodePacked, concat) receiving a BARE storage
/// bytes/string/array must materialize the storage value at the boundary.
contract StorageValueBoundaryTarget {
    bytes stored5;
    bytes stored31;
    bytes stored32;
    bytes stored33;
    string sstr;
    uint256[] arr;
    struct Box { uint256 a; bytes inner; }
    Box box;
    mapping(uint256 => bytes) mb;

    constructor() {
        stored5 = hex"1122334455";
        stored31 = hex"01020304050607080910111213141516171819202122232425262728293031";
        stored32 = hex"0102030405060708091011121314151617181920212223242526272829303132";
        stored33 = hex"010203040506070809101112131415161718192021222324252627282930313233";
        sstr = "hello";
        arr.push(7);
        arr.push(9);
        box.a = 1;
        box.inner = hex"aabbcc";
        mb[3] = hex"ddeeff";
    }

    function h5() public view returns (bytes32) { return keccak256(stored5); }
    function h31() public view returns (bytes32) { return keccak256(stored31); }
    function h32() public view returns (bytes32) { return keccak256(stored32); }
    function h33() public view returns (bytes32) { return keccak256(stored33); }
    function shaStored() public view returns (bytes32) { return sha256(stored5); }
    function henc() public view returns (bytes32) { return keccak256(abi.encode(arr)); }
    function hencp() public view returns (bytes32) { return keccak256(abi.encodePacked(arr)); }
    function hbox() public view returns (bytes32) { return keccak256(box.inner); }
    function hmap() public view returns (bytes32) { return keccak256(mb[3]); }
    // controls (worked before the fix; must stay identical)
    function hmem() public pure returns (bytes32) {
        bytes memory m = hex"1122334455";
        return keccak256(m);
    }
    function hstr() public view returns (bytes32) { return keccak256(bytes(sstr)); }
    function hpstored() public view returns (bytes32) { return keccak256(abi.encodePacked(stored5)); }
}
