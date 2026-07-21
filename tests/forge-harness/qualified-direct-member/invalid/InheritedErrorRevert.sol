pragma solidity ^0.8.0;
contract A { error E(uint256 x); }
contract B is A {}
contract T { function g() public pure { revert B.E(1); } }
