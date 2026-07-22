// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// SLICE-BOUND-NARROW-PANIC lane: a calldata-slice BOUND carrying narrow
// checked arithmetic (`uint8 a + b`) is evaluated by solc at ITS OWN type
// BEFORE the slice bounds check — overflow is Panic(0x11), never the slice's
// empty bounds revert. Covers `[lo:]`, `[:hi]`, and `[lo:hi]`.
contract SliceBoundNarrowPanicHarnessTarget {
    // Adjudicated repro: `msg.data[a+b:]` with a=200, b=100 -> Panic(0x11).
    function go(uint8 a, uint8 b) external pure returns (uint256) {
        bytes calldata s = msg.data[a + b:];
        return s.length;
    }

    // Stop-bound variant `[:a+b]`.
    function goStop(uint8 a, uint8 b) external pure returns (uint256) {
        bytes calldata s = msg.data[:a + b];
        return s.length;
    }

    // Both-bounds variant `[lo:hi]` on a calldata param.
    function goBoth(bytes calldata data, uint8 a, uint8 b)
        external
        pure
        returns (uint256)
    {
        bytes calldata s = data[a:a + b];
        return s.length;
    }
}
