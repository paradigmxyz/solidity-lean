pragma solidity ^0.8.0;
contract A { function f() private {} }
contract B { function f() private {} }
contract C is A, B {}
