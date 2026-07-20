// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
/* ===ARENA-MANIFEST===
{ "deploy": { "contract": "C", "args": [] }, "entry": { "function": "run", "args": [7] },
  "feature": "misc-precompiles-in-semantics",
  "note": "identity (0x4), modexp (0x5), bnAdd (0x6, incl. an off-curve ERROR case), bnMul (0x7) and blake2f (0x9, EIP-152 vector 5) staticcalls answered in-semantics. Must be NO_DIVERGENCE." }
===END-ARENA-MANIFEST=== */
contract C {
    function run(uint256 x) external view returns (uint256) {
        (bool ok4, bytes memory o4) =
            address(4).staticcall(abi.encodePacked(x, uint256(0xdead)));
        // modexp: 2^5 mod 13 = 6 (one-byte operands)
        (bool ok5, bytes memory o5) = address(5).staticcall(
            abi.encodePacked(uint256(1), uint256(1), uint256(1),
                uint8(2), uint8(5), uint8(13)));
        // bnAdd: G1 + G1 = 2*G1
        (bool ok6, bytes memory o6) = address(6).staticcall(
            abi.encode(uint256(1), uint256(2), uint256(1), uint256(2)));
        // bnAdd ERROR: (1,3) is not on the curve
        (bool ok6b, bytes memory o6b) = address(6).staticcall(
            abi.encode(uint256(1), uint256(3), uint256(1), uint256(2)));
        // bnMul: 9 * G1
        (bool ok7, bytes memory o7) = address(7).staticcall(
            abi.encodePacked(uint256(1), uint256(2), uint256(9)));
        // blake2f: EIP-152 vector 5 (12 rounds, blake2b-512("abc"))
        (bool ok9, bytes memory o9) = address(9).staticcall(
            hex"0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001");
        return uint256(keccak256(abi.encode(
            ok4, o4, ok5, o5, ok6, o6, ok6b, o6b, ok7, o7, ok9, o9)));
    }
}
