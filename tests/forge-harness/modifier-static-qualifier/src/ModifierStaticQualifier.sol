// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #157 MODIFIER-STATIC-QUALIFIER.
//
// A statically QUALIFIED modifier invocation `MsqBase.m` binds to the NAMED
// base's own modifier (solc `VirtualLookup::Static`), NOT the most-derived
// override. Deploying `MsqDerived` and calling `f()` runs MsqBase.m, so
// `tag == 1`. The UNQUALIFIED control `m` stays virtual and runs the override,
// so `MsqDerivedU.f()` leaves `tag == 2`.

contract MsqBase {
    uint public tag;
    modifier m() virtual { tag = 1; _; }
    function f() public MsqBase.m returns (uint) { return 7; } // qualified
}

contract MsqDerived is MsqBase {
    modifier m() override { tag = 2; _; }
}

contract MsqBaseU {
    uint public tag;
    modifier m() virtual { tag = 1; _; }
    function f() public m returns (uint) { return 7; } // unqualified (virtual)
}

contract MsqDerivedU is MsqBaseU {
    modifier m() override { tag = 2; _; }
}
