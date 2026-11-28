// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out: Clamp.sol renamed, with new constants in place of the stored bounds (the driver must
/// not depend on a contract's name, its storage layout or its literals).
contract Band {
    uint256 internal constant FLOOR = 17;
    uint256 internal constant CEIL = 4096;
    uint256 public reading;

    /// @custom:ensures reading == FLOOR
    constructor() {
        reading = FLOOR;
    }

    /// @custom:ensures result >= FLOOR && result <= CEIL
    /// @custom:ensures (x < FLOOR ==> result == FLOOR) && (x > CEIL ==> result == CEIL) && (FLOOR <= x && x <= CEIL ==> result == x)
    function fit(uint256 x) public pure returns (uint256 result) {
        if (x < FLOOR) return FLOOR;
        if (x > CEIL) return CEIL;
        return x;
    }

    /// @custom:ensures reading >= FLOOR && reading <= CEIL
    function record(uint256 x) external {
        reading = fit(x);
    }
}
