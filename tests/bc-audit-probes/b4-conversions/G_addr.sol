// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract G_addr {
    function u160RoundTrip() external pure returns (uint160) { uint160 v = 0x1234567890abcdef1234; return uint160(address(v)); }
    function b20FromAddr() external pure returns (uint160) { address a = address(uint160(0x1234567890abcdef1234)); bytes20 b = bytes20(a); return uint160(b); }
    function b20FromU160() external pure returns (uint160) { uint160 v = 0xffeeddccbbaa99887766; return uint160(bytes20(v)); }
}
