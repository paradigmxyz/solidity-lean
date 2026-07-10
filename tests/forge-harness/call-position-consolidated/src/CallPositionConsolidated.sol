// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CALL-POSITION CONSOLIDATED (#147-#151) — value-returning calls in argument-
// like positions. Each function exercises one locus; the internal helpers a()
// and b() record their evaluation into `ord` (base-10 digit trail) so the
// composed left-to-right order is observable, and return 3 / 4 respectively.
contract CallposConsolidatedT {
    uint256 public v;
    constructor(uint256 x) { v = x; }
}

contract CallPositionConsolidatedHarnessTarget {
    struct S { uint256 x; uint256 y; }
    uint256 public z;
    uint256 private ord;

    function a() internal returns (uint256) { ord = ord * 10 + 1; return 3; }
    function b() internal returns (uint256) { ord = ord * 10 + 2; return 4; }
    function inc(uint256 x) internal pure returns (uint256) { return x + 1; }

    // #147 — value-returning call in a modifier-invocation argument.
    modifier setZ(uint256 v_) { z = v_; _; }
    function modifierArg() external setZ(a()) returns (uint256) { return z; }
    // #147 — call nested (not bare) in a modifier-invocation argument.
    function modifierNestedArg() external setZ(a() + 1) returns (uint256) {
        return z;
    }

    // #148 — array-literal element calls `[a(), b()]`.
    function arrayLit() external returns (uint256) {
        uint256[2] memory arr = [a(), b()];
        return arr[0] * 10 + arr[1];
    }
    // #148 — eval order: a() before b() (trail = 12).
    function arrayLitOrder() external returns (uint256) {
        ord = 0;
        uint256[2] memory arr = [a(), b()];
        if (arr[0] * 10 + arr[1] == 34) { return ord; }
        return 999;
    }

    // #149 — struct-constructor argument calls `S(a(), b())`.
    function structArg() external returns (uint256) {
        S memory s = S(a(), b());
        return s.x * 10 + s.y;
    }
    // #149 — eval order: a() before b() (trail = 12).
    function structArgOrder() external returns (uint256) {
        ord = 0;
        S memory s = S(a(), b());
        if (s.x * 10 + s.y == 34) { return ord; }
        return 999;
    }

    // #150 — call in a `new` dynamic-array length argument (memory).
    function newArrayArg() external returns (uint256) {
        uint256[] memory arr = new uint256[](a());
        return arr.length;
    }
    // #150 — call in a `new bytes` length argument (nested in a binary).
    function newBytesArg() external returns (uint256) {
        bytes memory bb = new bytes(a() + 2);
        return bb.length;
    }
    // #150 — call in a `new` contract constructor argument (external creation).
    function newContractArg() external returns (uint256) {
        CallposConsolidatedT t = new CallposConsolidatedT(a());
        return t.v();
    }

    // #151 — call nested (not bare) in a function-call argument `inc(a() + 1)`.
    function nestedArg() external returns (uint256) {
        return inc(a() + 1);
    }
    // #151 — call nested inside an index argument `inc(arr[a() - 1])`.
    function nestedIndexArg() external returns (uint256) {
        uint256[3] memory arr = [uint256(7), 8, 9];
        return inc(arr[a() - 1]);
    }

    // Controls — call-free argument positions keep their prior lowering.
    function ctrlArray() external pure returns (uint256) {
        uint256[2] memory arr = [uint256(1), 2];
        return arr[0] * 10 + arr[1];
    }
    function ctrlStruct() external pure returns (uint256) {
        S memory s = S(1, 2);
        return s.x * 10 + s.y;
    }
    function ctrlNewArray() external pure returns (uint256) {
        uint256[] memory arr = new uint256[](4);
        return arr.length;
    }
}
