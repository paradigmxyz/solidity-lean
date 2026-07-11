// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #168 DELETE-MEMORY-NESTED-REF — `delete` on a MEMORY struct/array. solc 0.8.35
// allocates a brand-new, fully-zeroed object graph at the free-memory pointer, so
// a struct's dynamic-array member becomes a NEW empty (length-0) array, not an
// alias of the old one. `delete s` on `S { uint x; uint[] arr }` then reads back
// `(s.x, s.arr.length) == (0, 0)`. The model zeroed via `Value.defaultLike`, which
// has no Runtime and preserved the inner memory reference, so `s.arr.length` stayed
// 3 (wrong value). The fix walks the value graph runtime-aware, re-allocating every
// nested reference as a fresh zeroed cell, fully detached from the pre-delete cells
// (which a surviving alias keeps observing).
contract DeleteMemNestedRefHarness {
    struct S { uint x; uint[] arr; }
    struct Outer { S inner; uint[] tail; }
    struct V { uint a; uint b; }

    // Core: delete a struct with a dynamic-array member -> (0, 0).
    function f() external pure returns (uint, uint) {
        S memory s; s.x = 7; s.arr = new uint[](3); s.arr[0] = 42;
        delete s;
        return (s.x, s.arr.length);
    }

    // After delete, `s.arr` is a fresh array: a new allocation works -> (2, 5).
    function freshAfter() external pure returns (uint, uint) {
        S memory s; s.x = 7; s.arr = new uint[](3); s.arr[0] = 42;
        delete s;
        s.arr = new uint[](2); s.arr[1] = 5;
        return (s.arr.length, s.arr[1]);
    }

    // Fixed array of dynamic arrays: delete empties each inner array -> (0, 0).
    function g() external pure returns (uint, uint) {
        uint[][2] memory m;
        m[0] = new uint[](3); m[1] = new uint[](3);
        delete m;
        return (m[0].length, m[1].length);
    }

    // Nested struct: delete zeroes every nested length -> (0, 0, 0).
    function nested() external pure returns (uint, uint, uint) {
        Outer memory o;
        o.inner.x = 1; o.inner.arr = new uint[](3);
        o.tail = new uint[](4);
        delete o;
        return (o.inner.x, o.inner.arr.length, o.tail.length);
    }

    // Aliasing: a pre-delete alias `b` keeps the OLD array; `s.arr` is fresh -> (3, 42, 0).
    function aliasCase() external pure returns (uint, uint, uint) {
        S memory s; s.arr = new uint[](3); s.arr[0] = 42;
        uint[] memory b = s.arr;
        delete s;
        return (b.length, b[0], s.arr.length);
    }

    // Unchanged: delete a value-only struct -> (0, 0).
    function valueStruct() external pure returns (uint, uint) {
        V memory v; v.a = 3; v.b = 4;
        delete v;
        return (v.a, v.b);
    }

    // Unchanged: delete a top-level `uint[] memory` -> 0.
    function topArray() external pure returns (uint) {
        uint[] memory a = new uint[](3); a[0] = 9;
        delete a;
        return a.length;
    }

    // Unchanged: delete a scalar local -> 0.
    function scalarLocal() external pure returns (uint) {
        uint x = 7;
        delete x;
        return x;
    }
}
