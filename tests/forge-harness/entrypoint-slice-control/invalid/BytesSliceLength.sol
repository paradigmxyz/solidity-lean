// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BytesSliceLength {
    function bad(bytes calldata input) external pure returns (uint256) {
        return input[1:2].length;
    }
}
