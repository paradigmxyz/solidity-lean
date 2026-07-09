// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #63 (GET-STRUCT): a public state variable whose type is a struct with a
// NESTED struct member. solc's struct public-getter member-omission rule is
// SHALLOW: only a direct mapping/array member is omitted; a nested struct
// member (`inner`) is returned WHOLE, including the dynamic array it contains.
// The auto getter is therefore:
//   o() view returns (uint256 x, (uint256 a, uint256[] arr) inner)
contract GetterNestedStructHarnessTarget {
    struct Inner {
        uint256 a;
        uint256[] arr;
    }

    struct Outer {
        uint256 x;
        Inner inner;
    }

    Outer public o;

    function set(uint256 x, uint256 a, uint256[] memory arr) external {
        o.x = x;
        o.inner.a = a;
        o.inner.arr = arr;
    }
}
