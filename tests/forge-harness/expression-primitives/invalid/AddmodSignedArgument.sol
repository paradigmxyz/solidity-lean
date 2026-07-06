// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AddmodSignedArgument {
    function bad(int256 value, uint256 modulus)
        external
        pure
        returns (uint256)
    {
        return addmod(value, 2, modulus);
    }
}
