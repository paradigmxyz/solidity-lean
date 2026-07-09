// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// PRIV-SHADOW #69 reject: a private function whose name+parameter types collide
// with a base PUBLIC function of the same signature. The private side can never
// participate in an override, so solc rejects: "Overriding function is missing
// \"override\" specifier."

contract A {
    function f(uint) public {}
}

contract B is A {
    function f(uint) private {}
}
