// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A1 rational-constant ACCEPTS. solc 0.8.35 folds each constant in
// unbounded-precision signed rationals, then checks the folded value fits the
// declared type. The negative constants (N_NEG5 / N_SUB / N_FRACNEG) are the
// A1 over-reject regression guards: solc accepts them, and our checker did not
// until NumberRat was widened Nat -> Int.
contract RationalConstantsHarnessTarget {
    // fractional intermediates that resolve to an integer (int-trunc traps)
    uint256 public constant F_ETHER3 = (1 ether) / 3 * 3; // 1e18 (not 999...)
    uint256 public constant F_7_2_2 = 7 / 2 * 2;          // 7    (not 6)
    uint256 public constant M_HALFSUM = 1 / 2 + 1 / 2;    // 1    (not 0)

    // signed / negative folding — the A1 fix
    int256 public constant N_NEG5 = 0 - 5;                // -5
    int256 public constant N_SUB = 3 - 10;               // -7
    int256 public constant N_FRACNEG = 7 / 2 * 2 - 100;  // -93 (negative intermediate)
    int256 public constant N_UNARY = -3;                 // -3

    // fit boundary (exactly fits)
    uint8 public constant B_U8_255 = 255;                // 255  (max uint8)
    int8 public constant B_I8_MIN = -128;                // -128 (min int8)
}
