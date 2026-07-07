// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A fully-empty tuple target `(,)` is a parse error: at least one component
// must be present. solc rejects with "Expected primary expression."
contract Bad {
    function bad() external pure {
        uint256 a;
        uint256 b;
        a = 0;
        b = 0;
        (,) = (a, b);
    }
}
