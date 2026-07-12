// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// STAGE-D completion (#193/#194/#195): narrow checked arithmetic in
// abi.encode*/keccak256/concat ARGUMENTS (#193) and in LVALUE index KEYS (#194)
// must Panic 0x11 at the operand width; emit call-args must run in solc's
// two-phase order (#195).
contract StageDCompletion {
    uint256[400] arr;
    uint256[400][2] arr2;
    mapping(uint8 => uint256) mp;
    bytes bs;
    uint256 public trace;

    event E2(uint256 x, uint256 indexed y, uint256 z);
    event E3(uint256 indexed x, uint256 indexed y);
    event ED(uint256 x, uint256 y);

    // ---- #193: builtin/abi.encode* call arguments ----
    function h1(uint8 a, uint8 b) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(a + b));
    }
    function h2(uint8 a, uint8 b) external pure returns (bytes memory) {
        return abi.encode(a + b);
    }
    function h3(uint8 a, uint8 b) external pure returns (bytes memory) {
        return bytes.concat(bytes1(a + b));
    }
    function h4(uint8 a, uint8 b) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(a * b));
    }
    function h5(int8 a) external pure returns (bytes memory) {
        return abi.encode(-a);
    }
    // #193 controls (already MATCH; must stay)
    function c1(uint8 a, uint8 b) external pure returns (bytes32) {
        uint8 c = a + b; // statement-level narrow overflow panics here
        return keccak256(abi.encodePacked(c));
    }
    function c2(uint256 a, uint256 b) external pure returns (bytes memory) {
        return abi.encode(a + b); // 256-bit overflow already panics
    }
    function c3(uint8 a, uint8 b) external pure returns (bytes memory) {
        return abi.encode(a - b); // uint8 sub underflow (also underflows 256-bit)
    }
    function hSafe(uint8 a, uint8 b) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(a + b)); // safe values -> hash of a+b
    }

    // ---- #194: lvalue index keys ----
    function w1(uint8 a, uint8 b) external returns (uint256) {
        arr[a + b] = 7;
        return arr[300];
    }
    function w2(uint8 a, uint8 b) external returns (uint256) {
        mp[a + b] = 9;
        return mp[44];
    }
    function w3(uint8 a, uint8 b) external returns (uint256) {
        arr2[1][a + b] = 3;
        return arr2[1][300];
    }
    function w4(uint8 a, uint8 b) external returns (uint256) {
        bs = new bytes(400);
        bs[a + b] = 0x41;
        return uint256(uint8(bs[300]));
    }
    // #194 controls
    function wSafe(uint8 a, uint8 b) external returns (uint256) {
        arr[a + b] = 7; // safe key writes correctly
        return arr[a + b];
    }
    function rRead(uint8 a, uint8 b) external view returns (uint256) {
        return arr[a + b]; // read-side already panics (R2)
    }

    // ---- #195: emit call-arg two-phase schedule ----
    function f() internal returns (uint256) { trace = trace * 10 + 1; return trace; }
    function g() internal returns (uint256) { trace = trace * 10 + 2; return trace; }

    function emit2() external returns (uint256) {
        emit E2(f(), g(), f());
        return trace;
    }
    function emit3() external returns (uint256) {
        emit E3(f(), g());
        return trace;
    }
    // #195 control: all-non-indexed emit with call args stays L2R
    function emitData() external returns (uint256) {
        emit ED(f(), g());
        return trace;
    }
}
