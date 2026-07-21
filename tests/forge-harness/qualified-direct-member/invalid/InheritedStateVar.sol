pragma solidity ^0.8.0;
contract A { uint256 public v; }
contract B is A {}
contract C is B { function g() public view returns (uint256) { return B.v; } }
