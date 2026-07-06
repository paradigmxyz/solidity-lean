// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface DuplicateCatchErrorTarget {
    function fail() external;
}

contract DuplicateCatchError {
    function bad(DuplicateCatchErrorTarget target) external returns (uint256) {
        try target.fail() {
            return 1;
        } catch Error(string memory) {
            return 2;
        } catch Error(string memory) {
            return 3;
        }
    }
}
