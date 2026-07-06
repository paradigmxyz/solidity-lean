// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

struct FunctionField {
    function() internal pure returns (uint256) getter;
}

contract PublicStructInternalFunctionGetter {
    FunctionField public entry;
}
