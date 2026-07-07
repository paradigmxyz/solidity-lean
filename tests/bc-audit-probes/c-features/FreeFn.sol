// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
function freeAdd(uint256 a, uint256 b) pure returns (uint256) { return a + b; }
function freeMul(uint256 a, uint256 b) pure returns (uint256) { return a * b; }
contract FreeFn {
    function useFree(uint256 x, uint256 y) external pure returns (uint256) {
        return freeAdd(x, y) + freeMul(x, y);
    }
}
