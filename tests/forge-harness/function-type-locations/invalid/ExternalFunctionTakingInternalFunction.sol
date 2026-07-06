// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExternalFunctionTakingInternalFunction {
    function(function() internal pure returns (uint256)) external fp;
}
