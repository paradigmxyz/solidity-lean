// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract EnumIn {
    enum Color { Red, Green, Blue } // 0,1,2
    function inRange() external pure returns (uint8) { uint8 x = 2; Color c = Color(x); return uint8(c); }
    function outOfRange() external pure returns (uint8) { uint8 x = 3; Color c = Color(x); return uint8(c); }
    function zero() external pure returns (uint8) { uint8 x = 0; Color c = Color(x); return uint8(c); }
}
