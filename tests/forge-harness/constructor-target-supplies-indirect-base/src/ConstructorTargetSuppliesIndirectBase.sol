// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CTOR-RESIDUE reconciliation (gap #66): the deployment TARGET supplies an
// INDIRECT base's constructor arguments via a constructor MODIFIER, while the
// direct inheritor of that base supplies nothing.
//
// `Target is Mid is Base`. The deployment target is `Target`. Its direct base
// is `Mid`; `Mid`'s direct base is `Base`. `Mid` (the IMMEDIATE derived of
// `Base`) does NOT list `Base`'s arguments anywhere — it neither has an
// inheritance-specifier `Base(...)` nor a constructor modifier. Instead the
// most-derived contract `Target` supplies them via a constructor modifier
// `Base(3, 4)`, naming its INDIRECT base directly. solc permits the
// constructor-modifier form on any derived contract (not only the direct
// inheritor), and evaluates the arguments in that contract's frame.
//
// This is the minimal reduction of the OpenZeppelin harness pattern
// (`contract Harness is ERC721Enumerable { constructor() ERC721("n","s") {} }`)
// that the first CTOR-RESIDUE fix regressed: that fix read a base's
// modifier-supplied arguments only from the base's DIRECT inheritor (`Mid`
// here), found none, and matched `Base`'s two constructor parameters against
// zero arguments — an over-reject
//   (TypeError.arityMismatch "base constructor Base" 2 0).
// The reconciliation walks the whole linearization to find the contract that
// actually supplies each base's arguments (here the most-derived `Target`).

contract Base {
    uint256 public a;
    uint256 public b;
    constructor(uint256 x, uint256 y) {
        a = x;
        b = y;
    }
}

// `Mid` does not supply `Base`'s arguments, so solc requires it to be marked
// `abstract` (it can be inherited but not deployed directly) — exactly as the
// OpenZeppelin intermediates (`abstract contract ERC721Enumerable is ...`) are.
abstract contract Mid is Base {
    uint256 public m;
    constructor() {
        m = 7;
    }
}

contract Target is Mid {
    constructor() Base(3, 4) {}
}
