// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface DuplicateCatchPanicTarget {
    function fail() external;
}

contract DuplicateCatchPanic {
    function bad(DuplicateCatchPanicTarget target) external returns (uint256) {
        try target.fail() {
            return 1;
        } catch Panic(uint256 code) {
            return code;
        } catch Panic(uint256 code) {
            return code + 1;
        }
    }
}
