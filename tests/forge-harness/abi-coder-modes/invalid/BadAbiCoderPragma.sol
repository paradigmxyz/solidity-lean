// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma abicoder v3;

contract BadAbiCoderPragma {
    function ok() external pure returns (uint256) {
        return 1;
    }
}
