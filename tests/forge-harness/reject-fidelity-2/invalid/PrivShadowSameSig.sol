// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// PRIV-SHADOW #69 reject: a private function with the same name+parameter types
// as a base private function. A private function can never be virtual/override,
// so the cross-hierarchy same-signature collision is unsatisfiable. solc rejects:
// "Overriding function is missing \"override\" specifier."

contract A {
    function f(uint) private {}
}

contract B is A {
    function f(uint) private {}
}
