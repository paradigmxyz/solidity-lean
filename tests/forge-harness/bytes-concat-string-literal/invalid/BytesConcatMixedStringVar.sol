// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A string literal is accepted, but a mixed call with a `string`-typed value is
// still rejected (Error 8015). SB1 reject pin.
contract Bad {
    function bad(string memory s) external pure returns (bytes memory) {
        return bytes.concat("abc", s);
    }
}
