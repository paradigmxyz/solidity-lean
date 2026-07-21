pragma solidity ^0.8.0;
abstract contract A { modifier m() virtual; }
abstract contract A2 { modifier m() virtual; }
abstract contract B is A, A2 { modifier m() virtual override(A, A2) { _; } }
abstract contract C is A {}
abstract contract D is B, C {}
