// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// QUALIFIED-STRUCT-CONSTRUCTION — constructing a struct through a type-name
// qualifier where the struct is defined in ANOTHER (non-inherited) contract or
// a library: `A.S(1, 2)` (positional) and `A.S({x: 1, y: 2})` (named). solc
// accepts all of these; the qualified struct name resolves to the struct's
// constructor exactly as an unqualified in-scope struct name would. Both the
// library-scoped and contract-scoped forms, positional and named, are exercised.
library L {
    struct P {
        uint256 x;
        uint256 y;
    }
}

// A plain contract that merely DEFINES a struct; it is NOT inherited by the
// harness target below.
contract Defs {
    struct Q {
        uint256 a;
        uint256 b;
    }
}

contract QualifiedStructConstructionHarnessTarget {
    // library-scoped struct, positional constructor
    function libPositional() external pure returns (uint256) {
        L.P memory p = L.P(1, 2);
        return p.x + p.y; // 3
    }

    // library-scoped struct, named-field constructor (order swapped)
    function libNamed() external pure returns (uint256) {
        L.P memory p = L.P({y: 20, x: 10});
        return p.x * 1000 + p.y; // 10020
    }

    // contract-scoped (non-inherited) struct, positional constructor
    function contractPositional() external pure returns (uint256) {
        Defs.Q memory q = Defs.Q(4, 5);
        return q.a + q.b; // 9
    }

    // contract-scoped (non-inherited) struct, named-field constructor
    function contractNamed() external pure returns (uint256) {
        Defs.Q memory q = Defs.Q({a: 100, b: 200});
        return q.a * 1000 + q.b; // 100200
    }
}
