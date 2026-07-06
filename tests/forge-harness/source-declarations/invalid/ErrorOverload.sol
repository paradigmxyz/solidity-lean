// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ErrorOverload {
    error Bad(uint256 value);
    error Bad(address target);
}
