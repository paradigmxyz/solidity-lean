pragma solidity ^0.8.0;
abstract contract A { function f() public virtual; }
abstract contract A2 { function f() public virtual; }
abstract contract B is A, A2 { function f() public virtual override(A, A2) {} }
abstract contract C is A {}
abstract contract D is B, C {}
