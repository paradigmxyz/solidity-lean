// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// `T storage`-returning callee, USE-site sub-field operations on the returned
// reference. The callee shapes cover the whole-param return plus the formerly
// gated-out ones (nested member-path return, conditional/early return,
// storage-local return); the uses cover mapping write/read, ARRAY-FIELD
// push/push()/pop (the formerly over-rejected lowering), element write, length,
// and a plain field. Every accepted shape is pinned against the real EVM here.
library L3 {
    struct S { mapping(uint256 => uint256) m; uint256[] a; uint256 x; uint8[] b; }
    struct Outer { uint256 pad; S d; }

    function whole(S storage s) internal pure returns (S storage) {
        return s;
    }

    function memberOf(Outer storage o) internal view returns (S storage) {
        return o.d;
    }

    function pick(S storage a, S storage b, bool c) internal view returns (S storage) {
        if (c) { return a; }
        return b;
    }

    function viaLocal(S storage s) internal view returns (S storage) {
        S storage p = s;
        return p;
    }
}

contract StorageReturnSubfieldOpsHarnessTarget {
    L3.S internal s0;
    L3.S internal s1;
    L3.Outer internal outer;

    // mapping through each callee shape
    function mapWhole(uint256 k, uint256 v) external returns (uint256) {
        L3.whole(s0).m[k] = v;
        return L3.whole(s0).m[k];
    }

    function mapMember(uint256 k, uint256 v) external returns (uint256) {
        L3.memberOf(outer).m[k] = v;
        return L3.memberOf(outer).m[k];
    }

    function mapPick(uint256 k, uint256 v, bool c) external returns (uint256) {
        L3.pick(s0, s1, c).m[k] = v;
        return L3.pick(s0, s1, c).m[k];
    }

    // ARRAY-FIELD push value / push() / pop through the returned ref
    function pushWhole(uint256 v) external returns (uint256) {
        L3.whole(s0).a.push(v);
        return L3.whole(s0).a[0];
    }

    function pushMember(uint256 v) external returns (uint256) {
        L3.memberOf(outer).a.push(v);
        return L3.memberOf(outer).a[0];
    }

    function pushLocal(uint256 v) external returns (uint256) {
        L3.viaLocal(s1).a.push(v);
        return L3.viaLocal(s1).a[0];
    }

    function pushEmptyThenWrite(uint256 v) external returns (uint256) {
        L3.whole(s0).a.push();
        L3.whole(s0).a[0] = v;
        return s0.a[0];
    }

    function pushPushPop(uint256 v) external returns (uint256) {
        L3.memberOf(outer).a.push(v);
        L3.memberOf(outer).a.push(v + 1);
        L3.memberOf(outer).a.pop();
        return outer.d.a.length * 1000 + outer.d.a[0];
    }

    // plain field + length through returned refs
    function fieldPick(uint256 v, bool c) external returns (uint256) {
        L3.pick(s0, s1, c).x = v;
        return L3.pick(s0, s1, c).x;
    }

    function lenAfterPush(uint256 v) external returns (uint256) {
        L3.whole(s0).a.push(v);
        L3.whole(s0).a.push(v);
        return L3.whole(s0).a.length;
    }

    // NARROW-PUSH through the returned ref: uint8 checked addition must Panic
    // 0x11 on overflow (not silently wrap), and keep the narrow value intact
    // when it fits.
    function pushNarrow(uint8 x, uint8 y) external returns (uint256) {
        L3.memberOf(outer).b.push(x + y);
        return L3.memberOf(outer).b[0];
    }
}
