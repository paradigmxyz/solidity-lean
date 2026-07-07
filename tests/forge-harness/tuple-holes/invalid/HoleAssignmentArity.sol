// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A trailing hole does not absorb extra RHS components: a 2-slot LHS `(a, )`
// against a 3-tuple RHS is an arity/type mismatch. solc rejects.
contract Bad {
    function bad() external pure returns (uint256) {
        uint256 a;
        (a, ) = (1, 2, 3);
        return a;
    }
}
