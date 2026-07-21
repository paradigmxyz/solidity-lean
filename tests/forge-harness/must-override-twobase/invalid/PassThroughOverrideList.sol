pragma solidity ^0.8.0;
abstract contract A { function f() public virtual; }
abstract contract B is A { function f() public virtual override {} }
abstract contract C is A {}
abstract contract X is B, C {}
contract D is X { function f() public override(B) {} }
