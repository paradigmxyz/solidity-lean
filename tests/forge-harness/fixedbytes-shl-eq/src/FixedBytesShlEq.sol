// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// FB1: after `bytesN <<`, the result must be cleaned to the byte lane before a
// full-word comparison. `(b << 4) == bytes1(0xf0)` with `b = 0xff` is `true` on
// solc, because `b << 4` cleans to `0xf0`. Without the lane cleanup the escaped
// high bits make the comparison spuriously `false`.
contract FixedBytesShlEq {
    function shlEquals(bytes1 b) external pure returns (bool) {
        return (b << 4) == bytes1(0xf0);
    }
}
