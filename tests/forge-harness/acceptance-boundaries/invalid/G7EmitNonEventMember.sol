// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G7: qualified `emit X.g()` whose member is not an event — solc TypeError 9292.
contract G7Bad {
    event E();

    function g() internal pure {}

    function h() public {
        emit G7Bad.g();
    }
}
