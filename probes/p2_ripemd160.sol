// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
/* ===ARENA-MANIFEST===
{ "deploy": { "contract": "C", "args": [] }, "entry": { "function": "run", "args": [7] },
  "feature": "ripemd160-precompile-in-semantics",
  "note": "ripemd160 builtin (precompile 0x3) answered in-semantics: dynamic input (abi.encodePacked(x)), the empty string, and a >1-block input. Must be NO_DIVERGENCE." }
===END-ARENA-MANIFEST=== */
contract C {
    function run(uint256 x) external pure returns (uint256) {
        bytes20 a = ripemd160(abi.encodePacked(x));
        bytes20 b = ripemd160("");
        bytes20 c = ripemd160(abi.encodePacked(x, x, x));
        return uint256(keccak256(abi.encode(a, b, c)));
    }
}
