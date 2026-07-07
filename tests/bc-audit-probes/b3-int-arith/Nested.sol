// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Nested {
    // checked: inner 200+100=300 overflows uint8 -> solc panics 0x11 even though final 200 fits
    function u8IntermediateOverflow() external pure returns (uint8) { uint8 a=200; uint8 b=100; uint8 c=100; return a+b-c; }
    // checked: inner 100+100=200 no overflow, *2=400 overflows -> panic
    function u8MulChain() external pure returns (uint8) { uint8 a=100; uint8 b=100; uint8 c=2; return (a+b)*c; }
    // checked int8: inner 100+100=200 overflows int8 (max127) -> panic even if -c brings back
    function i8IntermediateOverflow() external pure returns (int8) { int8 a=100; int8 b=100; int8 c=100; return a+b-c; }
    // unchecked chain: (200+100)-100 = 44-100 wrap = ... check truncation-per-step vs final
    function u8UncheckedChain() external pure returns (uint8) { unchecked { uint8 a=200; uint8 b=100; uint8 c=100; return a+b-c; } }
    // unchecked mul chain: (200+100)*2 -> per-step 44*2=88 ; final-only 600&255=88 (same)
    function u8UncheckedMul() external pure returns (uint8) { unchecked { uint8 a=200; uint8 b=100; return (a+b)*2; } }
}
