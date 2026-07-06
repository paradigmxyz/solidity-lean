// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract LocalPointerDefinite {
    uint256[] private left;
    uint256[] private right;

    function storageStraight() external view returns (uint256) {
        uint256[] storage pointer;
        pointer = left;
        return pointer.length;
    }

    function storageBranch(bool choose) external view returns (uint256) {
        uint256[] storage pointer;
        if (choose) {
            pointer = left;
        } else {
            pointer = right;
        }
        return pointer.length;
    }

    function storageDoWhile() external view returns (uint256) {
        uint256[] storage pointer;
        do {
            pointer = right;
        } while (false);
        return pointer.length;
    }

    function pushThrough(uint256 value) external returns (uint256) {
        uint256[] storage pointer;
        pointer = left;
        pointer.push(value);
        return pointer[pointer.length - 1];
    }

    function calldataStraight(bytes calldata input)
        external
        pure
        returns (uint256)
    {
        bytes calldata pointer;
        pointer = input;
        return pointer.length;
    }

    function calldataBranch(bytes calldata first, bytes calldata second, bool choose)
        external
        pure
        returns (uint256)
    {
        bytes calldata pointer;
        if (choose) {
            pointer = first;
        } else {
            pointer = second;
        }
        return pointer.length;
    }

    function unusedPointers() external pure {
        uint256[] storage storagePointer;
        bytes calldata calldataPointer;
    }

    function shadowed(bytes calldata input) external pure returns (uint256) {
        bytes calldata pointer = input;
        {
            bytes calldata pointer;
        }
        return pointer.length;
    }
}
