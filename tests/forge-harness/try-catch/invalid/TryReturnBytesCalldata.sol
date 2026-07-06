// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryReturnBytesCalldataTarget {
    function data() external returns (bytes memory);
}

contract TryReturnBytesCalldata {
    function bad(TryReturnBytesCalldataTarget target) external returns (uint256) {
        try target.data() returns (bytes calldata data) {
            return data.length;
        } catch {
            return 0;
        }
    }
}
