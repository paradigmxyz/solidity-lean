// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

library L8 {
    function idm(uint8 v) internal pure returns (uint8) { return v; }
    function h(uint8 x) internal pure returns (uint8) { return x + 1; }
    function g(uint8 y) internal pure returns (uint8) { return y * 2; }
    function f(uint8 z) internal pure returns (uint8) { return z + 5; }
}

contract AuditProbe {
    event EMix(uint8 x, uint256 y);
    event EI(uint8 indexed x);
    event E2I(uint256 indexed x, uint256 indexed y);
    error Err(bytes d);
    struct P { uint8 v; }
    uint256 public cnt;
    uint8[] public arr8;
    mapping(uint8 => uint256) public m8;
    uint256[] public arr;

    constructor() {
        for (uint256 i = 0; i < 400; i++) { arr.push(i); }
        m8[44] = 7;
    }

    function bump() internal returns (uint256) { cnt += 1; return cnt; }
    function sink(uint8 v) external pure returns (uint8) { return v; }
    function sinkI(uint8 v) internal pure returns (uint8) { return v; }
    modifier mm(uint8 v) { _; }

    // ---- H-candidate positions: uint8 a=200,b=100 must Panic 0x11 ----
    function emitNamed(uint8 a, uint8 b) external returns (bool) {
        emit EMix({x: a + b, y: 1}); return true;
    }
    function revNamed(uint8 a, uint8 b) external pure returns (bool) {
        revert Err({d: abi.encode(a + b)});
    }
    function arrLit(uint8 a, uint8 b) external pure returns (uint8) {
        uint8[2] memory t = [a + b, 1]; return t[0];
    }
    function structCtor(uint8 a, uint8 b) external pure returns (uint8) {
        P memory p = P(a + b); return p.v;
    }
    function structNamed(uint8 a, uint8 b) external pure returns (uint8) {
        P memory p = P({v: a + b}); return p.v;
    }
    function newSize(uint8 a, uint8 b) external pure returns (uint256) {
        uint256[] memory t = new uint256[](a + b); return t.length;
    }
    function tupleAssign(uint8 a, uint8 b) external pure returns (uint8) {
        uint8 x; uint8 y; (x, y) = (a + b, b); return x + (y - y);
    }
    function tupleDecl(uint8 a, uint8 b) external pure returns (uint8) {
        (uint8 c, uint8 d) = (a + b, b); return c + (d - d);
    }
    function extArg(uint8 a, uint8 b) external view returns (uint8) {
        return this.sink(a + b);
    }
    function tryArg(uint8 a, uint8 b) external view returns (uint8) {
        try this.sink(a + b) returns (uint8 v) { return v; } catch { return 99; }
    }
    function libArg(uint8 a, uint8 b) external pure returns (uint8) {
        return L8.idm(a + b);
    }
    function usingArg(uint8 a, uint8 b) external pure returns (uint8) {
        return L8.f(L8.g(L8.h(a))) + (b - b);
    }
    function fnPtrArg(uint8 a, uint8 b) external pure returns (uint8) {
        function (uint8) internal pure returns (uint8) fp = sinkI;
        return fp(a + b);
    }
    function modArg(uint8 a, uint8 b) external mm(a + b) returns (bool) {
        return true;
    }
    function addmodArg(uint8 a, uint8 b) external pure returns (uint256) {
        return addmod(a + b, 1, 7);
    }
    function pushArg(uint8 a, uint8 b) external returns (uint256) {
        arr8.push(a + b); return arr8.length;
    }
    function idxNested(uint8 a, uint8 b) external view returns (uint256) {
        return arr[arr[a + b]];
    }
    function forInit(uint8 a, uint8 b) external pure returns (uint8) {
        uint8 s_ = 0;
        for (uint8 c = a + b; c > 0; c--) { s_ = 1; break; }
        return s_;
    }
    function delMapKey(uint8 a, uint8 b) external returns (bool) {
        delete m8[a + b]; return true;
    }
    function emitIndexed(uint8 a, uint8 b) external returns (bool) {
        emit EI(a + b); return true;
    }
    // unchecked wrap-width (wrong VALUE if env-less): expect 44
    function unchkVd(uint8 a, uint8 b) external pure returns (uint8) {
        unchecked { uint8 c = a + b; return c; }
    }
    function unchkTuple(uint8 a, uint8 b) external pure returns (uint8) {
        unchecked { (uint8 c, uint8 d) = (a + b, b); return c + (d - d); }
    }

    // ---- #196 nested internal/library call chains ----
    function h196(uint8 x) internal pure returns (uint8) { return x + 1; }
    function g196(uint8 y) internal pure returns (uint8) { return y * 2; }
    function f196(uint8 z) internal pure returns (uint8) { return z + 5; }
    function chain3(uint8 x) external pure returns (uint8) {
        return f196(g196(h196(x)));      // x=10 -> 27
    }
    function chain4(uint8 x) external pure returns (uint8) {
        return f196(f196(g196(h196(x)))); // x=10 -> 32
    }
    function chain3lib(uint8 x) external pure returns (uint8) {
        return L8.f(L8.g(L8.h(x)));      // x=10 -> 27
    }
    function chain3vd(uint8 x) external pure returns (uint8) {
        uint8 r = f196(g196(h196(x)));   // vardecl position, x=10 -> 27
        return r;
    }
    function chain3emit(uint8 x) external returns (bool) {
        emit EI(f196(g196(h196(x))));    // topic 27
        return true;
    }

    // ---- order controls ----
    function emit2Idx() external returns (uint256) {
        emit E2I(bump(), bump());        // indexed reverse: x=2, y=1
        return cnt;
    }
}
