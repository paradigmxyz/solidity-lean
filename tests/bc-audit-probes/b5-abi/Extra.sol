// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Extra {
    enum E { A, B, C }

    // solc: 1 byte 0x02 (enum packs to its underlying width = uint8)
    function packEnum() external pure returns (bytes memory) {
        return abi.encodePacked(E.C);
    }

    // solc: uint8[2] each padded to 32 bytes => 64 bytes (parity expected)
    function packU8Array() external pure returns (bytes memory) {
        uint8[2] memory a = [uint8(1), 2];
        return abi.encodePacked(a);
    }

    // solc: keccak("foo(uint256)")[:4] ++ 32-byte 0xab
    function encSig() external pure returns (bytes memory) {
        return abi.encodeWithSignature("foo(uint256)", uint256(0xab));
    }

    error Bad(uint256 x);
    error Empty();
}
