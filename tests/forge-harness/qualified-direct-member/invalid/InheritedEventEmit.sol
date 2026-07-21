pragma solidity ^0.8.0;
contract A { event Ev(uint256 x); }
contract B is A {}
contract T { function g() public { emit B.Ev(1); } }
