// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// OV1 over-accept repro (solc REJECTS): a free `f(uint256)` and a contract
// member `f(string)` share the name `f`. solc removes the free `f` from the
// contract's name scope (name-based shadowing, warning 2519), leaving only the
// member `f(string)` in scope. The bare call `f(5)` then has NO viable
// candidate (5 is not implicitly convertible to `string`), so solc reports
// "Invalid implicit conversion from int_const 5 to string memory requested."
// Before the OV1 fix, this frontend resolved `f(5)` to the shadowed free
// `f(uint256)` and wrongly accepted the program.
function f(uint256 a) pure returns (uint256) {
    return a + 1;
}

contract OverloadShadowReject {
    function f(string memory s) internal pure returns (uint256) {
        return bytes(s).length;
    }

    function g() internal pure returns (uint256) {
        return f(5);
    }
}
