// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract FirstAbstractBase {
    function value(uint256 input) public view virtual returns (uint256);
}

abstract contract SecondAbstractBase {
    function value(uint256 input) public view virtual returns (uint256);
}

abstract contract TwoAbstractConflict is FirstAbstractBase, SecondAbstractBase {}
