// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryReturnBytesNoLocationTarget {
    function data() external returns (bytes memory);
}

contract TryReturnBytesNoLocation {
    function bad(TryReturnBytesNoLocationTarget target) external returns (uint256) {
        try target.data() returns (bytes data) {
            return data.length;
        } catch {
            return 0;
        }
    }
}
