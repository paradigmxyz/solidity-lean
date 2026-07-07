// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract UncheckedNest {
    function nested() external pure returns (uint256) {
        unchecked {
            uint256 x = 1;
            unchecked {   // nested unchecked
                x = x - 2;
            }
            return x;
        }
    }
}
