// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Edge {
    function negBaseEven() external pure returns (int256) { int256 a=-2; return a**2; }
    function negBaseOdd() external pure returns (int256) { int256 a=-2; return a**3; }
    function shlWrapSigned() external pure returns (int8) { int8 a=64; return a<<1; }
    function shlTruncUnsigned() external pure returns (uint8) { uint8 a=255; return a<<1; }
}
