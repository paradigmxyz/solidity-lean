// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-family constant-folder ACCEPTS. solc 0.8.35 folds each constant in
// unbounded-precision signed rationals (ConstantEvaluator.cpp). Every constant
// here is one solidity-lean previously *over-rejected* (or, for P5/PZP/PNP, a program
// that could hang the importer) — the pinned compiler accepts and folds them to
// the value the getter returns.
contract CeFamilyHarnessTarget {
    // CE-1: negative constant exponents (and the 0**-1 = 0 base short-circuit).
    uint256 public constant P1 = 4 * 2 ** -1; // 2
    uint256 public constant P17 = 2 ** -2 * 16; // 4
    uint256 public constant P2 = 0 ** -1; // 0 (base-0 short-circuit)

    // CE-2a: unary ~ folded on integer rationals.
    int256 public constant P10 = ~5; // -6
    int256 public constant P15 = ~(-3); // 2
    int256 public constant X250 = ~5 & 0xFF; // 250

    // CE-3: negative operands in constant shifts/bitwise; SAR floors toward -inf.
    int256 public constant P6 = (-1) << 2; // -4
    int256 public constant P7 = -7 >> 1; // -4 (floor, not -3)
    int256 public constant P8 = -1 >> 100; // -1 (past-msb)
    int256 public constant P12 = -4 | 1; // -3

    // CE-4: fractional constant %.
    uint256 public constant P9 = 7 % 2.5; // 2

    // CE-5: fractional denominated literal.
    uint256 public constant P14 = 0.5 wei * 2; // 1

    // CE-6b: bases 0/1/-1 are exempt from the uint32 exponent cap, so these
    // compile without materializing the (astronomical) exponent.
    uint256 public constant P5 = 1 ** (2 ** 100); // 1
    uint256 public constant PZP = 0 ** (10 ** 60); // 0
    int256 public constant PNP = (-1) ** (2 ** 100); // 1 (even exponent)
}
