// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryReturnMismatchTarget {
    function get() external returns (uint256);
}

contract TryReturnMismatch {
    function bad(TryReturnMismatchTarget target) external returns (uint256) {
        try target.get() returns (bool flag) {
            return flag ? 1 : 0;
        } catch {
            return 0;
        }
    }
}
