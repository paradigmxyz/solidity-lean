// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Compound assignment (`+= -= *= <<= ...`) to a narrow (`< 256`-bit) int/uint
// LValue must apply the same type-width cleanup solc emits for the
// read-modify-write result: a checked cleanup (Panic 0x11 on overflow) for the
// arithmetic operators, and a *truncating* cast for `<<=` (which never
// overflow-checks, even inside a checked block). This target exercises every
// narrow-scalar LValue form (local, mapping value, array element, struct
// field) plus checked/unchecked controls and the already-correct uint256 case.
contract CompoundCleanupHarnessTarget {
    mapping(uint256 => uint8) private m;
    uint8[3] private arr;

    struct S {
        uint8 f;
    }

    S private s;

    // `16 << 4 == 256`, truncated to uint8 == 0 (no overflow check on `<<=`).
    function shlTrunc() external pure returns (uint8) {
        uint8 x = 16;
        x <<= 4;
        return x;
    }

    // 200 + 100 == 300 > 255 -> Panic 0x11 in checked mode.
    function addOverflow() external pure returns (uint8) {
        uint8 bal = 200;
        bal += 100;
        return bal;
    }

    // Same sum inside `unchecked` wraps: 300 & 0xff == 44.
    function addUncheckedWrap() external pure returns (uint8) {
        uint8 bal = 200;
        unchecked {
            bal += 100;
        }
        return bal;
    }

    // 16 * 17 == 272 > 255 -> Panic 0x11.
    function mulOverflow() external pure returns (uint8) {
        uint8 x = 16;
        x *= 17;
        return x;
    }

    // Control: 100 + 55 == 155, in range, no panic.
    function addNoOverflow() external pure returns (uint8) {
        uint8 x = 100;
        x += 55;
        return x;
    }

    // Mapping value LValue: 250 + 10 == 260 > 255 -> Panic 0x11.
    function mapOverflow() external returns (uint8) {
        m[1] = 250;
        m[1] += 10;
        return m[1];
    }

    // Mapping value LValue, unchecked: 260 & 0xff == 4.
    function mapUncheckedWrap() external returns (uint8) {
        m[1] = 250;
        unchecked {
            m[1] += 10;
        }
        return m[1];
    }

    // Array element LValue: 250 + 10 == 260 > 255 -> Panic 0x11.
    function arrOverflow() external returns (uint8) {
        arr[0] = 250;
        arr[0] += 10;
        return arr[0];
    }

    // Struct field LValue: 250 + 10 == 260 > 255 -> Panic 0x11.
    function structOverflow() external returns (uint8) {
        s.f = 250;
        s.f += 10;
        return s.f;
    }

    // Control: uint256 compound-assign must not gain a spurious width cleanup.
    function wideAddControl() external pure returns (uint256) {
        uint256 x = 1000000;
        x += 2000000;
        return x;
    }
}
