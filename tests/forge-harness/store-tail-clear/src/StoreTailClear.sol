// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// STORE-TAIL-CLEAR — a WHOLE-AGGREGATE storage assignment whose TOP layout is a
// `struct` or a `fixedArray` must, at every level, resize its dynamic-array
// members and ZERO the shrunk tail element slots (solc
// `copy_struct_to_storage` -> `copy_array_to_storage` -> `resize_array` ->
// `cleanup_storage_array_end` -> `clear_storage_range`, which clears whole slots
// from `dataStart + newLen` for `oldLen - newLen` slots). solidity-lean formerly
// tail-zeroed only when the TOP layout was itself a dynamic array; a struct or
// fixed-array top fell through to a plain store that wrote the new members +
// length but left the shrunk tail element slots STALE.
//
// The stale tail is not observable through length-bounded getters (a later
// `.push()` re-zeros), so the ground truth is the raw storage slots — the Lean
// lane reads them directly off the post-call state; the Forge side pins the
// solc/EVM getter values.
//
// NOTE (legacy pipeline): `struct[N] memory -> storage` is unsupported in legacy
// solc, so the fixed-array-of-struct case uses a storage->storage copy, and the
// fixed-array-of-dynamic-array case uses `uint[][N] memory -> storage`.
contract StoreTailClearHarnessTarget {
    struct S {
        uint256 a;
        uint256[] arr;
    }

    S sA;                 // slots 0 (a), 1 (arr length)
    S sB;                 // slots 2 (a), 3 (arr length)
    uint256[][2] fa;      // slots 4 (fa[0] length), 5 (fa[1] length)
    S[2] fsA;             // slots 6,7 (fsA[0]) and 8,9 (fsA[1])
    S[2] fsB;             // slots 10,11 (fsB[0]) and 12,13 (fsB[1])

    // F1a: whole-struct memory->storage; dyn-array member shrinks 5 -> 2.
    // Tail element slots keccak(1)+2..+4 must be zeroed.
    function structShrink() external returns (uint256, uint256, uint256) {
        sA.a = 99;
        sA.arr.push(10);
        sA.arr.push(20);
        sA.arr.push(30);
        sA.arr.push(40);
        sA.arr.push(50);
        S memory m;
        m.a = 7;
        m.arr = new uint256[](2);
        m.arr[0] = 100;
        m.arr[1] = 200;
        sA = m;                       // arr shrinks 5 -> 2, tail must clear
        return (sA.arr.length, sA.arr[0], sA.arr[1]);
    }

    // F1b: whole-struct storage->storage (`sA = sB`), same shrink.
    // Tail slots keccak(1)+2..+4 must be zeroed.
    function storageToStorageShrink() external returns (uint256, uint256, uint256) {
        sA.a = 11;
        sA.arr.push(1);
        sA.arr.push(2);
        sA.arr.push(3);
        sA.arr.push(4);
        sA.arr.push(5);
        sB.a = 8;
        sB.arr.push(111);
        sB.arr.push(222);            // sB.arr length 2
        sA = sB;                      // arr shrinks 5 -> 2, tail must clear
        return (sA.arr.length, sA.arr[0], sA.arr[1]);
    }

    // F2a: whole fixed-array-of-dynamic-array memory->storage (`uint[][2] = m`);
    // each inner dyn array shrinks 5 -> 2. Tail slots keccak(4)+2.. and
    // keccak(5)+2.. must be zeroed.
    function fixedArrayDynShrink() external returns (uint256, uint256, uint256, uint256) {
        for (uint256 i = 0; i < 5; i++) {
            fa[0].push(10 + i);
            fa[1].push(20 + i);
        }
        uint256[][2] memory m;
        m[0] = new uint256[](2);
        m[0][0] = 100;
        m[0][1] = 101;
        m[1] = new uint256[](2);
        m[1][0] = 200;
        m[1][1] = 201;
        fa = m;                       // both inner arrays shrink 5 -> 2
        return (fa[0].length, fa[0][1], fa[1].length, fa[1][1]);
    }

    // F2b/F3: whole fixed-array-of-struct storage->storage (`fsA = fsB`); each
    // inner struct's dyn-array member shrinks 5 -> 2. Tail slots keccak(7)+2..
    // and keccak(9)+2.. must be zeroed.
    function fixedArrayStructShrink() external returns (uint256, uint256, uint256, uint256) {
        for (uint256 i = 0; i < 5; i++) {
            fsA[0].arr.push(10 + i);
            fsA[1].arr.push(20 + i);
        }
        fsA[0].a = 1;
        fsA[1].a = 2;
        fsB[0].a = 3;
        fsB[0].arr.push(100);
        fsB[0].arr.push(101);
        fsB[1].a = 4;
        fsB[1].arr.push(200);
        fsB[1].arr.push(201);
        fsA = fsB;                    // both inner arrays shrink 5 -> 2
        return (fsA[0].arr.length, fsA[0].arr[1], fsA[1].arr.length, fsA[1].arr[1]);
    }

    // CONTROL: a whole-struct assignment that GROWS the dyn-array member (2 -> 4)
    // — no tail to clear; must not regress.
    function structGrow() external returns (uint256, uint256, uint256) {
        sA.a = 5;
        sA.arr.push(70);
        sA.arr.push(80);             // length 2
        S memory m;
        m.a = 6;
        m.arr = new uint256[](4);
        m.arr[0] = 1;
        m.arr[1] = 2;
        m.arr[2] = 3;
        m.arr[3] = 4;
        sA = m;                       // grows 2 -> 4
        return (sA.arr.length, sA.arr[2], sA.arr[3]);
    }
}
