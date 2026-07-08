// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G3: `==` on a reference type (dynamic bytes) — solc TypeError 2271.
contract G3Bytes {
    function f(bytes memory a, bytes memory b) public pure returns (bool) {
        return a == b;
    }
}
