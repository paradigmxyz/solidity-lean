// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Harness for the env-less narrow-int checked-overflow cleanup family
// (divergences #182 for-init loop counter, #183 array `.push(...)`, #184
// struct-constructor field on assign/vardecl). Each `*Overflow` entry is a
// narrow (`uint8`/`int8`) checked arithmetic value in one of the three leak
// positions; solc 0.8.35 + the EVM Panic 0x11 on overflow. The `*Cast` /
// `*Safe` / `*Wrap` entries pin the no-regression boundaries.
contract NarrowCleanupFamilyHarnessTarget {
    struct S { uint8 x; uint8 y; }
    uint8[] arr;
    uint8[][] arr2d;
    S st;

    // #182 for-init narrow loop counter (250 + i reaches 256 -> Panic 0x11).
    function forCounterOverflow() public pure returns (uint256 s) {
        for (uint8 i = 250; i < 300; i++) { s++; }
    }
    // no-regression: a safe counter counts fine.
    function forCounterSafe() public pure returns (uint256 s) {
        for (uint8 i = 0; i < 10; i++) { s++; }
    }
    // no-regression: unchecked narrow counter WRAPS 255->0 and terminates.
    function forCounterUncheckedWrap() public pure returns (uint256 s) {
        unchecked { for (uint8 i = 250; i != 5; i++) { s++; } }
    }

    // #183 push of narrow checked arithmetic.
    function pushAdd(uint8 a, uint8 c) public returns (uint8) {
        arr.push(a + c);
        return arr[arr.length - 1];
    }
    // no-regression: push of a genuine explicit truncating cast stays truncated.
    function pushCast(uint16 w) public returns (uint8) {
        arr.push(uint8(w));
        return arr[arr.length - 1];
    }
    // no-regression: push without overflow returns the value.
    function pushSafe(uint8 a) public returns (uint8) {
        arr.push(a);
        return arr[arr.length - 1];
    }
    // #183 nested 2d push.
    function push2dAdd(uint8 a, uint8 c) public returns (uint8) {
        arr2d.push();
        arr2d[0].push(a + c);
        return arr2d[0][0];
    }

    // #184 struct-constructor field on ASSIGN.
    function structAssignAdd(uint8 a, uint8 c) public returns (uint8) {
        st = S(a + c, 0);
        return st.x;
    }
    // #184 struct-constructor field on VARDECL (memory).
    function structVarDeclAdd(uint8 a, uint8 c) public pure returns (uint8) {
        S memory s = S(a + c, 0);
        return s.x;
    }
    // no-regression: struct-constructor field that is a genuine truncating cast.
    function structCast(uint16 w) public returns (uint8) {
        st = S(uint8(w), 0);
        return st.x;
    }
    // isolation: direct struct return already Panics on the return path.
    function structReturnAdd(uint8 a, uint8 c) public pure returns (S memory) {
        return S(a + c, 0);
    }
}
