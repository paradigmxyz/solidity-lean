// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G5: bare `return;` with a (named) non-empty return list — solc TypeError 6777.
contract G5 {
    function f() public pure returns (uint a) {
        return;
    }
}
