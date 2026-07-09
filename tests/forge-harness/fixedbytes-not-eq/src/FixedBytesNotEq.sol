// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// FB1: unary `~bytesN` must be cleaned to the byte lane (solc wraps `not(...)`
// in `cleanup_t_bytesN`). `(~b) == bytes1(0xf0)` with `b = 0x0f` is `true` on
// solc, because `~b` cleans to `0xf0`. Without the lane cleanup the complement
// sets every high bit and the comparison is spuriously `false`.
contract FixedBytesNotEq {
    function notEquals(bytes1 b) external pure returns (bool) {
        return (~b) == bytes1(0xf0);
    }
}
