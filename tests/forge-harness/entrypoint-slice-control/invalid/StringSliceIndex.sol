// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StringSliceIndex {
    function bad(string calldata input) external pure returns (bytes1) {
        return input[1:2][0];
    }
}
