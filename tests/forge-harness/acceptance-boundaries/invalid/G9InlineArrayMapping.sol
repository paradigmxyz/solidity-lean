// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G9: inline array literal of a mapping type — invalid memory type; solc rejects.
contract G9Bad {
    mapping(uint => uint) m;

    function f() public view {
        [m];
    }
}
