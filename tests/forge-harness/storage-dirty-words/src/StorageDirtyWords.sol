// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageDirtyWordsHarnessTarget {
    enum DirtyChoice {
        A,
        B,
        C
    }

    bool public flag; // slot 0
    uint256 private gap0; // slot 1
    DirtyChoice public choice; // slot 2
    uint256 private gap1; // slot 3
    address public who; // slot 4
    uint256 private gap2; // slot 5
    bytes4 public tag; // slot 6
    uint256 private gap3; // slot 7
    uint8 public u8v; // slot 8, offset 0
    int8 public i8v; // slot 8, offset 1

    function flagIsTrue() external view returns (bool) {
        return flag;
    }

    function choiceIsB() external view returns (bool) {
        return choice == DirtyChoice.B;
    }

    function choiceAsUint() external view returns (uint256) {
        return uint256(choice);
    }
}
