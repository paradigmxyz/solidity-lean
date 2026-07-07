// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// Rational-constant AUDIT probes (A1) — expected ACCEPTS.
// solc 0.8.35 folds each constant in unbounded-precision rationals, then checks
// the folded value fits the declared type. The folded value is visible in the
// AST as the `typeIdentifier` t_rational_<num>_by_<den> of each `value` node.
// Read back at runtime via the public getters in the Forge test.
contract Accepts {
    // --- scientific notation ---
    uint256 public constant SCI_1E18   = 1e18;                 // 1000000000000000000
    uint256 public constant SCI_1_5E3  = 1.5e3;                // 1500
    uint256 public constant SCI_2EM2X  = 2e-2 * 100;           // 2  (fractional intermediate 0.02)
    uint256 public constant SCI_10E0   = 10e0;                 // 10

    // --- sub-denominations ---
    uint256 public constant D_ETHER    = 1 ether;              // 1e18
    uint256 public constant D_GWEI     = 3 gwei;               // 3e9
    uint256 public constant D_MINUTES  = 2 minutes;            // 120
    uint256 public constant D_MIXTIME  = 2 minutes + 30 seconds; // 150
    uint256 public constant D_WEI      = 5 wei;                // 5

    // --- fractional intermediates that resolve to an integer ---
    uint256 public constant F_ETHER3   = (1 ether) / 3 * 3;    // 1e18 (999... if int-truncated!)
    uint256 public constant F_7_2_2    = 7 / 2 * 2;            // 7    (3.5*2; int-trunc gives 6)
    uint256 public constant F_10_4_4   = 10 / 4 * 4;           // 10   (int-trunc gives 8)

    // --- huge powers that cancel ---
    uint256 public constant P_256_255  = 2**256 / 2**255;      // 2
    uint256 public constant P_200_3    = (2**200 * 3) / 2**200; // 3

    // --- mixed rational / integer ---
    uint256 public constant M_ETHER5   = 1 ether + 5;          // 1000000000000000005
    uint256 public constant M_HALFSUM  = 1 / 2 + 1 / 2;        // 1   (0.5+0.5; int-trunc gives 0)

    // --- signed / negative folding ---
    int256  public constant N_NEG5     = 0 - 5;                // -5
    int256  public constant N_SUB      = 3 - 10;               // -7
    int256  public constant N_FRACNEG  = 7 / 2 * 2 - 100;      // -93  (negative intermediate)
    int256  public constant N_UNARY    = -3;                   // -3

    // --- fit boundary (exactly fits) ---
    uint8   public constant B_U8_255   = 255;                  // 255 (max uint8)
    int8    public constant B_I8_MIN   = -128;                 // -128 (min int8)
}
