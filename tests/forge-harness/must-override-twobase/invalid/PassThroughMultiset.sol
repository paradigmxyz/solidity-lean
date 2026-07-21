pragma solidity ^0.8.0;
abstract contract A3 { function f() public virtual; }
abstract contract A is A3 { function f() public virtual override; }
abstract contract B is A { function f() public virtual override {} }
abstract contract C is A {}
abstract contract X is B, C {}
abstract contract C3 is A3 {}
abstract contract D is X, C3 {}
