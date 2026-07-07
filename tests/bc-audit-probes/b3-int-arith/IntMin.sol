// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract IntMin {
    // int8 min / -1 : solc panics 0x11 (overflow) in checked
    function minDivNegOne() external pure returns (int8) {
        int8 a = type(int8).min;
        int8 b = -1;
        return a / b;
    }
    // -min : negation of int8 min overflows -> panic 0x11
    function negMin() external pure returns (int8) {
        int8 a = type(int8).min;
        return -a;
    }
    // unchecked min/-1 wraps to min
    function uncheckedMinDivNegOne() external pure returns (int8) {
        unchecked {
            int8 a = type(int8).min;
            int8 b = -1;
            return a / b;
        }
    }
}
