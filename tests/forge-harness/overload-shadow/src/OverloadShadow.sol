// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// OV1 over-reject repro (solc ACCEPTS): a free function `f(uint256)` and a
// contract member `f(uint256)` share both name and signature. solc removes the
// free `f` from the contract's name scope (name-based shadowing, warning 2519),
// so the bare call `f(5)` inside `g()` runs the MEMBER body (`s + 9` == 14),
// NOT the free body (`a + 1` == 6). This pins that the member wins.
function f(uint256 a) pure returns (uint256) {
    return a + 1;
}

contract OverloadShadowTarget {
    function f(uint256 s) internal pure returns (uint256) {
        return s + 9;
    }

    function g() public pure returns (uint256) {
        return f(5);
    }
}
