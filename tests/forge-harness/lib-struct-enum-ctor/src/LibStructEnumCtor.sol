// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #198: `Lib.S(Lib.Mode(m), 10)` — a qualified library struct constructor whose
// field type is a library-local enum. solc qualifies the field's declared type
// with the struct's OWNER (the library), so the qualified argument matches; the
// model formerly left the field type bare and over-rejected (poisoning the whole
// contract). Neighbors: unqualified/qualified ctor from INSIDE the library,
// named-args ctor, a foreign library struct holding another library's enum, and
// a storage write of the constructed value.
library Lib198 {
    enum Mode { Off, On, Auto }
    struct S { Mode m; uint256 v; }

    function make(uint8 m, uint256 v) internal pure returns (S memory) {
        return S(Mode(m), v);
    }

    function makeQ(uint8 m, uint256 v) internal pure returns (S memory) {
        return Lib198.S(Lib198.Mode(m), v);
    }
}

library Other198 {
    struct T { Lib198.Mode m; uint256 v; }
}

contract LibStructEnumCtorHarnessTarget {
    Lib198.S internal stored;

    // The exact #198 shape.
    function direct(uint8 m) external pure returns (uint256) {
        Lib198.S memory s = Lib198.S(Lib198.Mode(m), 10);
        return uint256(s.m) + s.v;
    }

    function viaLib(uint8 m) external pure returns (uint256) {
        Lib198.S memory s = Lib198.make(m, 10);
        return uint256(s.m) + s.v;
    }

    function viaLibQ(uint8 m) external pure returns (uint256) {
        Lib198.S memory s = Lib198.makeQ(m, 10);
        return uint256(s.m) + s.v;
    }

    function named(uint8 m) external pure returns (uint256) {
        Lib198.S memory s = Lib198.S({m: Lib198.Mode(m), v: 10});
        return uint256(s.m) + s.v;
    }

    function foreignEnumField(uint8 m) external pure returns (uint256) {
        Other198.T memory t = Other198.T(Lib198.Mode(m), 10);
        return uint256(t.m) + t.v;
    }

    function storedWrite(uint8 m) external returns (uint256) {
        stored = Lib198.S(Lib198.Mode(m), 10);
        return uint256(stored.m) + stored.v;
    }
}
