// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// File-level (free) error, same NAME as several contract errors, different sig.
error Bad(bool);

library Lib {
    error Bad(bytes32);
}

// #139 ERROR-SELECTOR-COLLISION: two sibling contracts each declare `error Bad`
// with a DIFFERENT signature and each returns its OWN `Bad.selector`. The model
// built a single GLOBAL flat name->selector table, so the same-name/diff-sig
// collision made the bare `Bad.selector` unresolvable (lookup returned none),
// and the whole contract failed to lower (over-reject). solc scopes the bare
// selector PER CONTRACT: A.s() is Bad(uint256), B.s() is Bad(address).
contract A {
    error Bad(uint256);
    function s() public pure returns (bytes4) {
        return Bad.selector; // 0xa2f43130
    }
}

contract B {
    error Bad(address);
    function s() public pure returns (bytes4) {
        return Bad.selector; // 0x830c4ac2 — NOT poisoned by A's Bad
    }
    // Type-qualified selector still resolves to the DECLARING (library) scope
    // even though the bare name collides three ways.
    function q() public pure returns (bytes4) {
        return Lib.Bad.selector; // 0x30665c7b
    }
}

contract Base {
    error Bad(uint256);
}

// Bare selector on an INHERITED error must resolve to the base's error, not a
// sibling contract's same-name error.
contract Derived is Base {
    function s() public pure returns (bytes4) {
        return Bad.selector; // inherited Bad(uint256) = 0xa2f43130
    }
}

// Bare selector where the only visible `Bad` is the FILE-LEVEL (free) error.
contract UsesFree {
    function s() public pure returns (bytes4) {
        return Bad.selector; // free Bad(bool) = 0x381f6d34
    }
}
