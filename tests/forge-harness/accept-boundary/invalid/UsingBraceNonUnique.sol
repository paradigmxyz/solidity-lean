// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// USINGFOR-BRACE #82 reject: the brace-form using-for name must resolve
// uniquely. Two free `f` overloads make `{f}` ambiguous. solc rejects:
// "Identifier is not a function name or not unique."

type T is uint256;

function f(T a) pure returns (uint) {
    return T.unwrap(a);
}

function f(bool b) pure returns (bool) {
    return b;
}

using {f} for T;

contract C {
    function g(T a) public pure returns (uint) {
        return a.f();
    }
}
