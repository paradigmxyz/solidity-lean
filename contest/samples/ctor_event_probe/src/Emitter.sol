// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract Emitter {
    event Ctor(uint256 x);
    event Ran(uint256 y);
    constructor() { emit Ctor(1); }
    function f() external { emit Ran(2); }
}
