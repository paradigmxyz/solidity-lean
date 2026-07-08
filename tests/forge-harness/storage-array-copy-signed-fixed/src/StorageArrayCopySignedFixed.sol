// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// R2 — the rest of the storage-array-copy convert family that G14 deferred:
// SIGNED element widening (int8[] -> int16[]) and FIXED-length destinations
// (T[N] = S[M], N >= M) including signed. solc accepts these
// (ArrayType::isImplicitlyConvertibleTo, Types.cpp:1628-1665): base implicitly
// convertible, dynamic dest any length / fixed dest N>=M; runtime resizes,
// sign/zero-extends each element to the dest width, and zero-fills / pads the
// tail.
contract StorageArrayCopySignedFixedHarnessTarget {
    int8[]    srcI8;
    int16[]   dstI16;
    int8[3]   srcI8Fixed;
    int16[5]  dstI16Fixed;
    uint8[2]  srcU8Fixed;
    uint16[4] dstU16Fixed;

    // int8[] -> int16[]: sign-extend each element to 16 bits (never overflows).
    function signedWiden() external returns (int256, int256, int256) {
        srcI8.push(-5); srcI8.push(127);
        dstI16 = srcI8;
        return (int256(dstI16[0]), int256(dstI16[1]), int256(dstI16.length));
    }

    // int8[3] -> int16[5]: N=5 > M=3, elements sign-extended, tail padded 0.
    function fixedDestSigned() external returns (int256, int256, int256, int256, int256) {
        srcI8Fixed[0] = -1; srcI8Fixed[1] = 100; srcI8Fixed[2] = -128;
        dstI16Fixed = srcI8Fixed;
        return (dstI16Fixed[0], dstI16Fixed[1], dstI16Fixed[2], dstI16Fixed[3], dstI16Fixed[4]);
    }

    // uint8[2] -> uint16[4]: N=4 > M=2, zero-extend, tail padded 0.
    function fixedDestUnsigned() external returns (uint256, uint256, uint256, uint256) {
        srcU8Fixed[0] = 200; srcU8Fixed[1] = 255;
        dstU16Fixed = srcU8Fixed;
        return (dstU16Fixed[0], dstU16Fixed[1], dstU16Fixed[2], dstU16Fixed[3]);
    }
}
