// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (bytes memory) {
        return abi.encodeWithSignature(uint256(1), uint256(2));
    }
}
