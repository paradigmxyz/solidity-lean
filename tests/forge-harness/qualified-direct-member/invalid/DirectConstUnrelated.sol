pragma solidity ^0.8.0;
contract A { uint256 public constant K = 7; }
contract T { function g() public pure returns (uint256) { return A.K; } }
