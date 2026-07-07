// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Nested {
    struct Inner { uint128 x; uint128 y; }      // packs into 1 slot
    struct Outer { Inner[2] arr; uint256 tag; }  // arr occupies 2 slots, tag next
    Outer[3] outers;                             // struct-in-array-in-... base

    // mapping-in-struct
    struct WithMap { uint256 head; mapping(uint256 => uint256) m; uint256 tail; }
    WithMap wm;

    // fixed-size array packing: uint64[4] fits in 1 slot
    uint64[4] packedArr;

    // bytesN in struct
    struct BytesStruct { bytes1 b1; bytes4 b4; bytes32 b32; }
    BytesStruct bs;

    function setNested(uint256 i, uint256 j, uint128 x, uint128 y, uint256 tag) external {
        outers[i].arr[j].x = x;
        outers[i].arr[j].y = y;
        outers[i].tag = tag;
    }
    function getNestedX(uint256 i, uint256 j) external view returns (uint128) { return outers[i].arr[j].x; }
    function getNestedY(uint256 i, uint256 j) external view returns (uint128) { return outers[i].arr[j].y; }
    function getNestedTag(uint256 i) external view returns (uint256) { return outers[i].tag; }

    function setMap(uint256 h, uint256 k, uint256 v, uint256 t) external {
        wm.head = h; wm.m[k] = v; wm.tail = t;
    }
    function getMapHead() external view returns (uint256) { return wm.head; }
    function getMapVal(uint256 k) external view returns (uint256) { return wm.m[k]; }
    function getMapTail() external view returns (uint256) { return wm.tail; }

    function setPackedArr(uint64 a0, uint64 a1, uint64 a2, uint64 a3) external {
        packedArr[0]=a0; packedArr[1]=a1; packedArr[2]=a2; packedArr[3]=a3;
    }
    function getPackedArr(uint256 i) external view returns (uint64) { return packedArr[i]; }

    function setBS(bytes1 b1, bytes4 b4, bytes32 b32) external { bs.b1=b1; bs.b4=b4; bs.b32=b32; }
    function getBS1() external view returns (bytes1) { return bs.b1; }
    function getBS4() external view returns (bytes4) { return bs.b4; }
    function getBS32() external view returns (bytes32) { return bs.b32; }
}
