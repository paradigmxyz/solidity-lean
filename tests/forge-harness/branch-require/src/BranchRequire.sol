// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract BranchRequireHarnessTarget {
    uint256 private value;

    function choose(uint256 x) external {
        if (x < 10) {
            value = x;
        } else {
            value = 10;
        }
    }

    function read() external view returns (uint256) {
        return value;
    }

    function requireSmall(uint256 x) external pure returns (uint256) {
        require(x < 10, "too large");
        return x + 1;
    }

    function assertSmall(uint256 x) external pure returns (uint256) {
        assert(x < 10);
        return x + 1;
    }

    function assertAndWrite(bool ok) external returns (uint256) {
        value = 7;
        assert(ok);
        return value;
    }
}
