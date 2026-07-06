// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AddressMemberTarget {}

contract AddressMemberReceivers {
    function balanceOf(address target) external view returns (uint256) {
        return target.balance;
    }

    function codeLength(address target) external view returns (uint256) {
        return target.code.length;
    }

    function codehashOf(address target) external view returns (bytes32) {
        return target.codehash;
    }

    function identity(address target) external pure returns (address) {
        return target;
    }
}
