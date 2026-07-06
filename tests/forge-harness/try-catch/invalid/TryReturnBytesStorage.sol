// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryReturnBytesStorageTarget {
    function data() external returns (bytes memory);
}

contract TryReturnBytesStorage {
    function bad(TryReturnBytesStorageTarget target) external returns (uint256) {
        try target.data() returns (bytes storage data) {
            return data.length;
        } catch {
            return 0;
        }
    }
}
