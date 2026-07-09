// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// AGG3: a fixed array of a sub-32-byte value type never straddles a slot: it
// occupies `floor(32/width)` elements per slot and spans `ceil(len/perSlot)`
// slots. `uint40[32]` = 6 slots (not 5), so the variable AFTER it must land
// at the correct, higher slot.
contract AggregateArraySpanHarnessTarget {
    uint256 private head;      // slot 0
    uint40[32] private f1;     // slots 1..6 (6-slot span, floor(32/5)=6 per slot)
    uint8 private tail1;       // slot 7

    function setAll() external returns (uint256) {
        head = 1;
        f1[0] = 0xaa;
        f1[31] = 0xbb;
        tail1 = 0x99;
        return tail1;
    }

    function readAll() external view returns (uint256, uint40, uint40, uint8) {
        return (head, f1[0], f1[31], tail1);
    }
}
