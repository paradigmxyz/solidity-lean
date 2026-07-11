// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A storage argument is ambiguous between f(memory) and f(storage): solc rejects
// with "No unique declaration found after argument-dependent lookup".
contract AmbiguousStorageArg {
    uint256[] private s;
    function f(uint256[] memory x) internal pure returns (uint256) { return x.length + 100; }
    function f(uint256[] storage x) internal view returns (uint256) { return x.length + 200; }
    function callStorage() external view returns (uint256) { return f(s); }
}
