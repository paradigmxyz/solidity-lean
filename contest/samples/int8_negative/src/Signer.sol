// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: a negative int8 return. EVM ABI SIGN-EXTENDS -5 to a full
// 32-byte word (0xff..fb); solidity-lean must decode/render it as the same
// signed integer -> success|i:-5. A sign-extension / render mismatch (e.g.
// rendering as w:251 or the raw word) would be a fake wrong-value gap.
contract Signer {
    function f(int8 a) external pure returns (int8) {
        return a;
    }
}
