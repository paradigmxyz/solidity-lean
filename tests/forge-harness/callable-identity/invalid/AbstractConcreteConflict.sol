// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract AbstractBase {
    function value(uint256 input) public view virtual returns (uint256);
}

contract ConcreteBase {
    function value(uint256 input) public view virtual returns (uint256) {
        return input + 1;
    }
}

abstract contract AbstractConcreteConflict is AbstractBase, ConcreteBase {}
