// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CTOR-RESIDUE gap (a): base-constructor arguments supplied by an INTERMEDIATE
// contract's own constructor-modifier list.
//
// `MidD is MidC is MidB`. The deployment target is `MidD`, which supplies its
// direct base `MidC`'s argument via `MidC(5)`. `MidC` in turn supplies its own
// direct base `MidB`'s argument via a constructor MODIFIER `MidB(y * 2)`, where
// `y` is `MidC`'s constructor parameter (bound to 5 during construction).
//
// solc resolves each contract's base-constructor arguments wherever that
// contract declares them (constructor modifier here), evaluated in that
// contract's frame: `MidB`'s argument `y * 2` is evaluated with `y == 5`, so
// `bVal == 10` and `cVal == 5`.
//
// The pre-fix lowering resolved base arguments only from the deployment
// TARGET's own modifiers / inheritance list, so `MidB`'s argument (declared on
// the intermediate `MidC`) was never found: `MidB`'s single constructor
// parameter was matched against zero arguments and the whole constructor failed
// to lower (over-reject). The fix reads each base's arguments from the direct
// inheritor and evaluates them in that inheritor's constructor frame.

contract MidB {
    uint256 public bVal;
    constructor(uint256 x) {
        bVal = x;
    }
}

contract MidC is MidB {
    uint256 public cVal;
    constructor(uint256 y) MidB(y * 2) {
        cVal = y;
    }
}

contract MidD is MidC {
    constructor() MidC(5) {}
}
