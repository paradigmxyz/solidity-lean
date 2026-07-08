// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// CL1: solc REJECTS a bare modifier-style base-constructor call (error 1563,
// "Modifier-style base constructor call without arguments.") -- the base must
// be invoked as `Base()` (or given arguments in the inheritance list), never as
// a bare `Base`. Importer-masked in the differential harness (solc emits no AST
// for this program), so this fixture only lives on the solc-reject side.
contract Base {
    uint256 public x;
    constructor() {
        x = 1;
    }
}

contract Derived is Base {
    constructor() Base {}
}
