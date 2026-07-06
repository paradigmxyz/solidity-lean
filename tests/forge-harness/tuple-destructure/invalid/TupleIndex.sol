// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TupleIndex {
    function pair() internal pure returns (uint256, uint256) {
        return (1, 2);
    }

    function badLiteralTupleIndex() external pure returns (uint256) {
        return (uint256(1), uint256(2))[0];
    }

    function badReturnTupleIndex() external pure returns (uint256) {
        return pair()[0];
    }
}
