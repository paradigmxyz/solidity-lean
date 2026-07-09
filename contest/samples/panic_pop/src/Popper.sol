// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: .pop() on an empty storage array must revert with
// Panic(0x31) (0x31 = 49). Distinct panic path (storage-array underflow) from
// overflow(0x11)/div-zero(0x12)/enum(0x21)/OOB(0x32)/assert(0x01). Exercises a
// state-mutating (non-view) entry + empty dynamic storage array. A code
// mismatch or a non-panic revert here would be a fake wrong-revert gap.
contract Popper {
    uint256[] private arr;

    function f() external returns (uint256) {
        arr.pop();
        return arr.length;
    }
}
