// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
/* ===ARENA-MANIFEST===
{ "deploy": { "contract": "C", "args": [] }, "entry": { "function": "run", "args": [7] },
  "feature": "ecrecover-precompile-in-semantics",
  "note": "ecrecover builtin (precompile 0x1) answered in-semantics: canonical go-ethereum recovery vector (expects 0x7156526fbd7a3c72969b54f64e42c10fbb768c8a), the v=27 lifting variant, and an invalid v=29 (expects address(0)). Must be NO_DIVERGENCE." }
===END-ARENA-MANIFEST=== */
contract C {
    function run(uint256 x) external pure returns (uint256) {
        bytes32 h = 0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3;
        bytes32 r = 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608;
        bytes32 s = 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada;
        address a = ecrecover(h, 28, r, s);
        address b = ecrecover(h, 27, r, s);
        address c = ecrecover(h, 29, r, s);
        return uint256(keccak256(abi.encode(a, b, c, x)));
    }
}
