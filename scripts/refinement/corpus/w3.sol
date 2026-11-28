// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    function f(address a) external pure returns (uint160) {
        return uint160(a) ^ 1;
    }
}
