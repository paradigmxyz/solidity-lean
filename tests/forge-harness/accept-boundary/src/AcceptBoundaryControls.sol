// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// ACCEPT-BOUNDARY accepted controls: the "must still accept" neighbours of the
// two reject-fidelity fixes. Every declaration here is accepted by pinned solc
// 0.8.35 and by the Lean checker (pinned in Witness/TypeCheck.lean via
// acceptBoundaryDisciplineMatches).

// Base-constructor args supplied in ONLY ONE place (the inheritance list) — not
// a double supply. Accepted.
contract Base {
    constructor(uint) {}
}

contract SingleSupply is Base(1) {
    constructor() {}
}

// Brace-form using-for whose binding IS attachable and unique. Accepted.
type T is uint256;

function attach(T a) pure returns (uint) {
    return T.unwrap(a);
}

using {attach} for T;

// Library-form using-for is validated LAZILY: an unused library function whose
// self type does not match the target is accepted (only the brace form is
// eager).
library L {
    function mismatched(bool b) internal pure returns (bool) {
        return b;
    }
}

using L for T;

contract Surface {
    function use(T a) public pure returns (uint) {
        return attach(a);
    }
}
