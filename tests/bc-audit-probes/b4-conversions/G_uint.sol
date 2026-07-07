// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract G_uint {
    // uint8(uint256 var) truncates low byte: 0x1234 -> 0x34 = 52
    function u8FromU256() external pure returns (uint8) { uint256 a = 0x1234; return uint8(a); }
    // uint128(2^200+7) -> 7
    function u128FromU256() external pure returns (uint128) {
        uint256 x = 0x100000000000000000000000000000000000000000000000007;
        return uint128(x);
    }
    // uint256(int256 var = -1) -> 2^256-1
    function u256FromI256Neg1() external pure returns (uint256) { int256 a = -1; return uint256(a); }
}
