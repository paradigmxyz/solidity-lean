// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TryLowLevelCall {
    function bad(address target) external returns (uint256) {
        try target.call(abi.encodeWithSignature("ping()")) {
            return 1;
        } catch {
            return 0;
        }
    }
}
