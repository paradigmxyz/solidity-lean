// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// WS2 (#146 / #177) STORAGE-REF EARLY BINDING: solc computes the concrete
/// slot of a storage pointer ONCE at the binding access (running the bounds
/// check there), then raw-sloads with NO length recheck. A pointer bound to a
/// dynamic-array element therefore survives `pop()` shrink: dereferencing it
/// reads (or writes) the freed, pop-zeroed slot instead of Panicking 0x32.
contract StorageRefEarlyBindTarget {
    struct S {
        uint256 a;
        uint256 b;
    }

    S[] internal arr;
    mapping(uint256 => S) internal m;
    uint256[] internal nums;

    /// t1: pop-then-deref (the #146/#177 divergence): reads the freed
    /// (pop-zeroed) slot -> 0. Late-binding models Panic 0x32 here.
    function t1() external returns (uint256) {
        arr.push();
        arr.push();
        arr[1].a = 7;
        S storage p = arr[1];
        arr.pop();
        return p.a;
    }

    /// t2: pop-then-push-then-deref control (already matched) -> 9.
    function t2() external returns (uint256) {
        arr.push();
        arr.push();
        arr[1].a = 7;
        S storage p = arr[1];
        arr.pop();
        arr.push();
        arr[1].a = 9;
        return p.a;
    }

    /// t3: out-of-bounds at the BINDING access still Panics 0x32.
    function t3() external returns (uint256) {
        arr.push();
        S storage p = arr[2];
        return p.a;
    }

    /// t3code: the Panic code observed for t3 (0x32 = 50).
    function t3code() external returns (uint256) {
        try this.t3() returns (uint256) {
            return 1;
        } catch Panic(uint256 code) {
            return code;
        }
    }

    /// t4: mutation through ANOTHER path is visible through the pointer
    /// (early binding fixes the SLOT, not the value) -> 33.
    function t4() external returns (uint256) {
        arr.push();
        arr.push();
        S storage p = arr[1];
        arr[1].a = 33;
        return p.a;
    }

    /// t5: mapping-value pointer write-through control -> 88.
    function t5() external returns (uint256) {
        S storage p = m[3];
        p.a = 88;
        return m[3].a;
    }

    /// t6: WRITE through the pointer after shrink, read it back through the
    /// captured slot -> 5 (the write lands in the freed slot).
    function t6() external returns (uint256) {
        arr.push();
        arr.push();
        S storage p = arr[1];
        arr.pop();
        p.a = 5;
        return p.a;
    }

    // ---- #188 write-through re-pins (storage-ref RETURNS from paths) ----

    function refS(uint256 i) internal view returns (S storage) {
        return arr[i];
    }

    function refM(uint256 k) internal view returns (S storage) {
        return m[k];
    }

    function refN() internal view returns (uint256[] storage) {
        return nums;
    }

    /// t7: indexed storage-ref return write-through -> 42.
    function t7() external returns (uint256) {
        arr.push();
        arr.push();
        S storage s = refS(1);
        s.a = 42;
        return arr[1].a;
    }

    /// t8: mapping-value storage-ref return write-through -> 88.
    function t8() external returns (uint256) {
        S storage q = refM(5);
        q.b = 88;
        return m[5].b;
    }

    /// t9: uint[] storage-ref return, push through the returned ref -> 55.
    function t9() external returns (uint256) {
        refN().push(55);
        return nums[0];
    }
}
