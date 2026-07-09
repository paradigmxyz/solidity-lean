// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// USINGFOR-BRACE #82 reject: the brace-form using-for is validated eagerly. `f`
// takes a `bool`, which the target type `T` cannot implicitly convert to, so it
// cannot be attached. solc rejects: "The function \"f\" cannot be attached to
// the type \"T\" because the type cannot be implicitly converted to the first
// argument of the function."

type T is uint256;

function f(bool x) pure returns (bool) {
    return x;
}

using {f} for T;

contract C {
    function g() public pure returns (uint) {
        return 1;
    }
}
