// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RefsResidueFnValues} from "../src/RefsResidueFnValues.sol";

// Forge ground truth for the boundary-completion arc residue closure:
// member-form internal function VALUES and function-pointer VALUES created in
// constructor and modifier bodies.
contract RefsResidueFnValuesForgeTest {
    // Member-form library internal fn value used as an argument dispatches to
    // the same function a direct call would: applyF(MathLib.dbl, 21) == 42.
    function testViaLibMember() public {
        RefsResidueFnValues t = new RefsResidueFnValues(true);
        require(t.viaLibMember(21) == 42, "viaLibMember");
    }

    // Member-form contract internal fn value: applyF(This.trip, 4) == 12.
    function testViaContractMember() public {
        RefsResidueFnValues t = new RefsResidueFnValues(true);
        require(t.viaContractMember(4) == 12, "viaContractMember");
    }

    // Function-pointer VALUE created in the CONSTRUCTOR body, called later.
    function testViaCtorPointer() public {
        require(new RefsResidueFnValues(true).viaCtorPointer(21) == 42, "ctor dbl");
        require(new RefsResidueFnValues(false).viaCtorPointer(4) == 12, "ctor trip");
    }

    // Function-pointer VALUE created in a MODIFIER body, called in the body.
    function testViaModifierPointer() public {
        RefsResidueFnValues t = new RefsResidueFnValues(true);
        require(t.viaModifierPointer(10) == 11, "viaModifierPointer");
    }
}
