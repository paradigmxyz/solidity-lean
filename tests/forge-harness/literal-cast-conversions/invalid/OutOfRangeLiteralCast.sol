// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc rejects an explicit conversion of an out-of-range *raw* integer literal:
// "Explicit type conversion not allowed from int_const 300 to uint8."
contract OutOfRangeLiteralCast {
    function bad() external pure returns (uint8) {
        return uint8(300);
    }
}
