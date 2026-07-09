// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Harness-hardening probe: a revert reason with NON-UTF-8 bytes (0xff 0xfe),
// built via abi.encodePacked so it bypasses source-literal UTF-8. The revert
// DATA is identical on both engines (deterministic Error(string) encoding); the
// only question is whether the HARNESS renders those identical bytes the same on
// both sides. EVM side does utf-8 decode(errors="replace") -> U+FFFD; if the Lean
// render differs, an identical revert fabricates a wrong-revert gap (false positive).
contract BadStr {
    function f() external pure returns (uint256) {
        revert(string(abi.encodePacked(bytes1(0xff), bytes1(0xfe), "ok")));
    }
}
