// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma experimental UnknownFeature;

contract BadExperimentalPragma {
    function ok() external pure returns (uint256) {
        return 1;
    }
}
