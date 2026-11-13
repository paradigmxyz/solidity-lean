// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// `bytesN` constants keep their width at every use: values of different widths
// compare and combine left-aligned, and `f().length` still runs `f`.
contract FixedBytesConstantWidthsHarnessTarget {
    bytes2 constant Y = 0x1234;
    bytes4 constant X = 0x12345678;
    bytes4 constant Z = 0x12340000;
    bytes1 constant B = 0x12;
    bytes8 constant X8 = 0x1234567800000000;
    bytes4 constant YW = Y;
    bytes4 constant XY = X | Y;
    bool constant EQ = Y == Z;
    bool constant WIDE_EQ = X == X8;

    uint256 private calls;

    function compared() external pure returns (bool) {
        return EQ;
    }

    function widenedCompare() external pure returns (bool) {
        return WIDE_EQ;
    }

    function widened() external pure returns (bytes4) {
        return YW;
    }

    function combined() external pure returns (bytes4) {
        return XY;
    }

    function selected() external pure returns (bytes4) {
        bytes4 value = false ? X : Y;
        return value;
    }

    function compareParam(bytes4 value) external pure returns (bool) {
        return Y == value;
    }

    function constantLength() external pure returns (uint256) {
        return X.length;
    }

    function packedHash() external pure returns (bytes32) {
        return keccak256(abi.encodePacked(Y, B));
    }

    function encodedHash() external pure returns (bytes32) {
        return keccak256(abi.encode(Y));
    }

    function sideEffect() external returns (uint256, uint256) {
        return (makeBytes().length, calls);
    }

    function makeBytes() private returns (bytes4) {
        calls += 1;
        return 0;
    }
}
