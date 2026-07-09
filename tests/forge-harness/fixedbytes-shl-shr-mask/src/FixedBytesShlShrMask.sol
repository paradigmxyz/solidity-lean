// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// FB1: `bytesN <<` must re-clean its result to the byte lane (solc
// `cleanup_t_bytesN` around `shl`). `(b << 4) >> 4` on `bytes1(0xff)` is `0x0f`
// on solc: the `<<` drops the escaped high nibble before the `>>` shifts it
// back down. Without the lane cleanup the escaped bits survive the `<<` and the
// `>>` recovers them, wrongly yielding `0xff`.
contract FixedBytesShlShrMask {
    function shlThenShr(bytes1 b) external pure returns (bytes1) {
        return (b << 4) >> 4;
    }
}
