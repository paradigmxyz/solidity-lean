// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
contract AllTen {
    function run(uint256 x) external view returns (bytes32, uint256) {
        bytes32 acc;
        uint256 okBits;
        {
            (bool ok, bytes memory o) = address(1).staticcall(
                abi.encode(x, uint256(27), uint256(1), uint256(1)));
            if (ok) okBits |= 1;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            (bool ok, bytes memory o) = address(2).staticcall(abi.encode(x));
            if (ok) okBits |= 2;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            (bool ok, bytes memory o) = address(3).staticcall(abi.encode(x));
            if (ok) okBits |= 4;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            (bool ok, bytes memory o) = address(4).staticcall(
                abi.encode(x, x + 1));
            if (ok) okBits |= 8;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // modexp: 2^5 mod 13 = 6 (one-byte operands)
            (bool ok, bytes memory o) = address(5).staticcall(
                abi.encodePacked(uint256(1), uint256(1), uint256(1),
                    uint8(2), uint8(5), uint8(13)));
            if (ok) okBits |= 16;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // bnAdd: G1 + G1 = 2*G1
            (bool ok, bytes memory o) = address(6).staticcall(
                abi.encode(uint256(1), uint256(2), uint256(1), uint256(2)));
            if (ok) okBits |= 32;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // bnMul: 9 * G1
            (bool ok, bytes memory o) = address(7).staticcall(
                abi.encodePacked(uint256(1), uint256(2), uint256(9)));
            if (ok) okBits |= 64;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // bnPairing: empty input -> success, output word 1
            (bool ok, bytes memory o) = address(8).staticcall("");
            if (ok) okBits |= 128;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // blake2f: EIP-152 vector 5 (12 rounds, blake2b-512("abc"))
            (bool ok, bytes memory o) = address(9).staticcall(
                hex"0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001");
            if (ok) okBits |= 256;
            acc = keccak256(abi.encode(acc, o));
        }
        {
            // pointEvaluation (0xa): the trivial zero-polynomial proof —
            // commitment = proof = the compressed point at infinity, y = 0.
            bytes memory commitment = new bytes(48);
            commitment[0] = 0xc0;
            bytes32 vh = sha256(commitment);
            vh = bytes32((uint256(vh) & ((uint256(1) << 248) - 1))
                | (uint256(1) << 248));
            (bool ok, bytes memory o) = address(10).staticcall(
                abi.encodePacked(vh, bytes32(0), bytes32(0), commitment,
                    commitment));
            if (ok) okBits |= 512;
            acc = keccak256(abi.encode(acc, o));
        }
        return (acc, okBits);
    }
}
