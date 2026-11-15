// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract KeccakMem {
    function salt(address token0, address token1) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(token0, token1));
    }
}
