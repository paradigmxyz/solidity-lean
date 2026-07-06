// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryFunctionType {
    function(L) internal pure returns (uint256) private callback;
}
