// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExternalFunctionTakingMapping {
    function(mapping(uint256 => uint256) storage values) external fp;
}
