// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// R3 #188: an internal/library fn returning a storage POINTER from an
/// INDEXED/MEMBER path (arr[i], m[k], o.inner) must re-point the caller's
/// alias so writes go through to storage.
library RefLib {
    struct S { uint256 a; uint256 b; }
    function at(S[] storage self, uint256 i) internal view returns (S storage) {
        return self[i];
    }
    function bump(S storage self) internal {
        self.a = 42;
    }
}

contract StorageRefPathReturnTarget {
    struct O { RefLib.S inner; }
    using RefLib for RefLib.S[];
    using RefLib for RefLib.S;

    RefLib.S[] arr;
    mapping(uint256 => RefLib.S) m;
    mapping(uint256 => uint256[]) mu;
    O o;

    constructor() {
        arr.push(RefLib.S(1, 2));
        arr.push(RefLib.S(3, 4));
        mu[5].push(30);
        m[7] = RefLib.S(5, 6);
    }

    function refS(uint256 i) internal view returns (RefLib.S storage) { return arr[i]; }
    function refM(uint256 k) internal view returns (RefLib.S storage) { return m[k]; }
    function refU() internal view returns (uint256[] storage) { return mu[5]; }
    function refInner() internal view returns (RefLib.S storage) { return o.inner; }
    function refWhole() internal view returns (RefLib.S[] storage) { return arr; }

    // array element path
    function t1() public returns (uint256) {
        RefLib.S storage s = refS(1);
        s.a = 42;
        return arr[1].a;
    }
    // returned ref used directly as an lvalue base (ANF-hoisted temp)
    function t2() public returns (uint256) {
        refS(0).b = 77;
        return arr[0].b;
    }
    // mapping value path
    function t3() public returns (uint256) {
        RefLib.S storage s = refM(7);
        s.b = 88;
        return m[7].b;
    }
    // uint[] storage value through a mapping; push through the returned ref
    function t4() public returns (uint256) {
        uint256[] storage p = refU();
        p.push(55);
        return mu[5][1];
    }
    // nested member path
    function t5() public returns (uint256) {
        RefLib.S storage s = refInner();
        s.a = 42;
        return o.inner.a;
    }
    // CONTROL: whole-var return (worked before the fix)
    function t6() public returns (uint256) {
        RefLib.S[] storage p = refWhole();
        p[0].a = 99;
        return arr[0].a;
    }
    // using-for library boundary returning a storage ref from a path
    function t7() public returns (uint256) {
        RefLib.S storage s = arr.at(1);
        s.a = 42;
        return arr[1].a;
    }
    // library receiver write-through on a returned ref
    function t8() public returns (uint256) {
        arr.at(0).bump();
        return arr[0].a;
    }
}
