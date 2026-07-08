// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// UF1: a file-level `using ... for T global;` directive admits ANY user-defined
// type defined in the same source unit as T -- struct, enum, or UDVT. Only a
// built-in / elementary type (8841) or a cross-file type (4117) is rejected.
// A *struct* attached globally to free functions via the brace form is a
// mainstream library idiom that pinned solc 0.8.35 accepts.

struct Amount {
    uint256 value;
}

function doubled(Amount memory a) pure returns (uint256) {
    return a.value * 2;
}

function plus(Amount memory a, uint256 b) pure returns (uint256) {
    return a.value + b;
}

// `using {f, g} for S global;` on a STRUCT (not a UDVT).
using {doubled, plus} for Amount global;

enum Color {
    Red,
    Green,
    Blue
}

function rank(Color c) pure returns (uint256) {
    return uint256(c) + 1;
}

// `using {f} for E global;` on an ENUM (not a UDVT).
using {rank} for Color global;

contract UsingForGlobalNonUdvt {
    function computeDoubled(uint256 x) public pure returns (uint256) {
        Amount memory a = Amount(x);
        return a.doubled();
    }

    function computePlus(uint256 x, uint256 y) public pure returns (uint256) {
        Amount memory a = Amount(x);
        return a.plus(y);
    }
}
