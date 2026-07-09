// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Exercises (a) constructor + state-variable initializer storage being present
// before the entry call, and (b) BROAD storage divergence auto-detection: the
// claim declares NO observed_slots, yet slots written by the initializer (slot0),
// the constructor (slot1), the entry call (slot2), and a mapping entry (a hashed
// slot) are all compared automatically on both engines.
contract CtorSt {
    uint256 public slot0 = 11;              // initializer  -> slot 0
    uint256 public slot1;                   // constructor  -> slot 1
    uint256 public slot2;                   // entry call   -> slot 2
    mapping(uint256 => uint256) public m;   // hashed slot (keccak(key, 3))

    constructor() {
        slot1 = 22;
    }

    function run(uint256 x) external returns (uint256) {
        slot2 = x;
        m[x] = x + 100;
        return slot0 + slot1 + slot2;       // 11 + 22 + x
    }
}
