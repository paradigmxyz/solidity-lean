// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Boundary-completion arc — residue closure (2026-07-07):
//   * member-form internal function VALUES (`Lib.f`, `Contract.f`) used as a
//     function-pointer argument dispatch to the SAME function a direct call
//     would;
//   * function-pointer VALUES created in a CONSTRUCTOR body and in a MODIFIER
//     body, later called through the runtime dispatch ID.
library MathLib {
    function dbl(uint256 x) internal pure returns (uint256) { return 2 * x; }
    function inc(uint256 x) internal pure returns (uint256) { return x + 1; }
}

contract RefsResidueFnValues {
    function(uint256) internal pure returns (uint256) fp;     // set in constructor
    function(uint256) internal pure returns (uint256) fpMod;  // set in modifier

    function trip(uint256 x) internal pure returns (uint256) { return 3 * x; }

    function applyF(
        function(uint256) internal pure returns (uint256) f,
        uint256 x
    ) internal pure returns (uint256) {
        return f(x);
    }

    // Constructor: a function-pointer VALUE (library member-form OR bare
    // identifier, data-dependent) written to a state variable.
    constructor(bool useDbl) {
        fp = useDbl ? MathLib.dbl : trip;
    }

    // Member-form LIBRARY internal fn value as an argument: == MathLib.dbl(x).
    function viaLibMember(uint256 x) public pure returns (uint256) {
        return applyF(MathLib.dbl, x);
    }

    // Member-form CONTRACT internal fn value as an argument: == trip(x).
    function viaContractMember(uint256 x) public pure returns (uint256) {
        return applyF(RefsResidueFnValues.trip, x);
    }

    // Call the constructor-created pointer.
    function viaCtorPointer(uint256 x) public view returns (uint256) {
        return fp(x);
    }

    modifier setMod() {
        fpMod = MathLib.inc;   // function-pointer VALUE created in a modifier body
        _;
    }

    // Call a pointer created/used in a modifier body: == MathLib.inc(x).
    function viaModifierPointer(uint256 x) public setMod returns (uint256) {
        return fpMod(x);
    }
}
