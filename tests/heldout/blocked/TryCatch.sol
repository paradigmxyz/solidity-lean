// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract TryCatch {
    uint256 public last;

    /// @notice ensures last == 1 || last == 2
    function probe(address target) external {
        try this.ping(target) returns (uint256) {
            last = 1;
        } catch {
            last = 2;
        }
    }

    function ping(address) external pure returns (uint256) {
        return 1;
    }
}
