// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Held-out loop for the loop certificate checker, written for it independently of the
// verify_counter example: a while loop counting down, a local accumulator and a return value.
contract Drain {
    uint256 public total;

    /// @custom:requires n <= 1000000 && total <= 1000000
    /// @custom:ensures moved == 2 * n
    /// @custom:ensures total == old(total) + 2 * n
    function drain(uint256 n) external returns (uint256 moved) {
        uint256 k = n;
        moved = 0;
        while (k > 0) {
            k -= 1;
            moved += 2;
        }
        total += moved;
    }
}
