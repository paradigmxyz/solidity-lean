// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A trailing-hole declaration `(uint a, )` binds one slot; against a 3-tuple
// RHS the component counts differ. solc rejects: "Different number of
// components on the left hand side (2) than on the right hand side (3)."
contract Bad {
    function bad() external pure returns (uint256) {
        (uint256 a, ) = (1, 2, 3);
        return a;
    }
}
