// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: the shift amount 2**33 exceeds uint32 max — checked before the lhs==0
// short-circuit, so even 0 << 2**33 is rejected.
contract ShiftExponentCap {
    uint256 public constant BAD = 0 << 2 ** 33;
}
