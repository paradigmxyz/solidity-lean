// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// PRIV-SHADOW #69 accept controls: a private OVERLOAD (same name, different
// params) across the hierarchy, and a legitimate public virtual/override — both
// accepted by solc AND solidity-lean.

contract A {
    function f(uint) private {}
    function g(uint) public virtual {}
}

contract B is A {
    function f(uint, uint) private {}   // overload: different params -> OK
    function g(uint) public override {} // legitimate override -> OK
}
