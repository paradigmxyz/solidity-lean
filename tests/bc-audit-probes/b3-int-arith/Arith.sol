// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Arith {
    // signed division truncates toward zero: -7/2 = -3
    function divTruncNeg() external pure returns (int256) { int256 a=-7; int256 b=2; return a/b; }
    // signed mod takes sign of dividend: -7%3 = -1
    function modNegDividend() external pure returns (int256) { int256 a=-7; int256 b=3; return a%b; }
    function modPosDivNeg() external pure returns (int256) { int256 a=7; int256 b=-3; return a%b; }   // = 1
    function modNegNeg() external pure returns (int256) { int256 a=-7; int256 b=-3; return a%b; }      // = -1
    // int256.min % -1 = 0 (no panic)
    function minModNegOne() external pure returns (int256) { int256 a=type(int256).min; int256 b=-1; return a%b; }
    // 0**0 = 1
    function zeroPowZero() external pure returns (uint256) { uint256 a=0; uint256 b=0; return a**b; }
    // right assoc: 2**3**2 = 512
    function powRightAssoc() external pure returns (uint256) { uint256 a=2; return a**3**2; }
    // negative base even/odd power
    function negBaseEven() external pure returns (int256) { int256 a=-2; return a**2; }   // 4
    function negBaseOdd() external pure returns (int256) { int256 a=-2; return a**3; }     // -8
    // unchecked 2**256 wraps to 0
    function uncheckedPow256() external pure returns (uint256) { unchecked { uint256 a=2; return a**256; } }
    // left shift wraps (no overflow check): int8(64)<<1 = -128
    function shlWrapSigned() external pure returns (int8) { int8 a=64; return a<<1; }
    // uint8 shift left overflow truncates: uint8(255)<<1 = 254
    function shlTruncUnsigned() external pure returns (uint8) { uint8 a=255; return a<<1; }
    // shift >= width : uint256 1<<256 = 0
    function shlGeWidth() external pure returns (uint256) { uint256 a=1; uint256 s=256; return a<<s; }
    // arithmetic shift right signed: -8 >> 1 = -4
    function sarNeg() external pure returns (int256) { int256 a=-8; return a>>1; }
    // -1 >> 255 = -1
    function sarNegOneBig() external pure returns (int256) { int256 a=-1; uint256 s=255; return a>>s; }
    // signed shift right by >= width: -1 >> 256 = -1 ; 5 >> 256 = 0
    function sarGeWidthNeg() external pure returns (int256) { int256 a=-1; uint256 s=256; return a>>s; }
    function sarGeWidthPos() external pure returns (int256) { int256 a=5; uint256 s=256; return a>>s; }
    // narrowing reinterpret int8(uint8(200)) = -56
    function narrowReinterpret() external pure returns (int8) { uint8 a=200; return int8(a); }
    // uint8(257) = 1 (truncate)
    function narrowTrunc() external pure returns (uint8) { uint256 a=257; return uint8(a); }
}
