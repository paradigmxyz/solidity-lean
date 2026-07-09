// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #63 (GET-STRUCT) ACCEPTED control: pins the shallow-omission boundary.
// Top-level omission drops the direct mapping (`m`) and direct array
// (`dropped`) but keeps the value member (`keep`) and the string member
// (`label`); the nested pure-value struct (`inner`) is returned WHOLE. The auto
// getter is:
//   s() view returns (uint256 keep, string label, (uint256 a, uint256 b) inner)
contract GetterStructRejectHarnessTarget {
    struct Inner {
        uint256 a;
        uint256 b;
    }

    struct S {
        uint256 keep;
        string label;
        mapping(uint256 => uint256) m;
        uint256[] dropped;
        Inner inner;
    }

    S public s;

    function setup(uint256 keep, string memory label, uint256 a, uint256 b)
        external
    {
        s.keep = keep;
        s.label = label;
        s.inner.a = a;
        s.inner.b = b;
    }
}
