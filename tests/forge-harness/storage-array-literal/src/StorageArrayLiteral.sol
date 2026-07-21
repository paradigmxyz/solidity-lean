// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// ITEM-1 (front-end over-rejection): inline array literals whose elements are
// storage `bytes`/`string` state variables, storage-pointer locals, or storage
// dynamic arrays, used in value positions (abi.encode*, keccak256, emit,
// revert). solc implicitly copies each element to memory; the model's
// normalizer + runtime value-use materializer handle the lowered shape, but
// the front-end used to fail to TYPE the literal (no env-aware element
// typing) and over-rejected the whole function.
contract StorageArrayLiteralHarnessTarget {
    bytes b1;
    bytes b2;
    string s1;
    string s2;
    uint256[] a1;

    event EBytes(bytes[2] arr);
    error EArr(bytes[2] arr);

    // abi.encode([b1, b2]) : bytes[2] with storage bytes elements.
    // b1 = hex"aa", b2 = hex"bbcc":
    // enc = [0x20][0x40][0x80][1][aa..][2][bbcc..] = 224 bytes;
    // enc[159] = 0xaa (last byte of the b1 tail's first word... probed below)
    function encBytes() external returns (uint256) {
        b1 = hex"aa";
        b2 = hex"bbcc";
        bytes memory e = abi.encode([b1, b2]);
        return e.length * 1000000 + uint256(uint8(e[128])) * 1000
            + uint256(uint8(e[192]));
    }

    // abi.encode([s1, s2]) : string[2] with storage string elements.
    function encStrings() external returns (uint256) {
        s1 = "hey";
        s2 = "yo";
        bytes memory e = abi.encode([s1, s2]);
        return e.length * 1000000 + uint256(uint8(e[128])) * 1000
            + uint256(uint8(e[192]));
    }

    // Storage-pointer locals nested in the literal.
    function encPointers() external returns (uint256) {
        b1 = hex"aa";
        b2 = hex"bbcc";
        bytes storage p1 = b1;
        bytes storage p2 = b2;
        bytes memory e = abi.encode([p1, p2]);
        return e.length * 1000000 + uint256(uint8(e[128])) * 1000
            + uint256(uint8(e[192]));
    }

    // keccak256 over the encoded literal equals the memory twin.
    function hashMatches() external returns (uint256) {
        s1 = "hey";
        s2 = "yo";
        string[2] memory twin = [string("hey"), "yo"];
        bool eq = keccak256(abi.encode([s1, s2]))
            == keccak256(abi.encode(twin));
        return eq ? 1 : 0;
    }

    // Storage dynamic-array elements: uint256[][2].
    function encArrays() external returns (uint256) {
        a1.push(7);
        a1.push(9);
        bytes memory e = abi.encode([a1, a1]);
        return e.length * 1000000 + uint256(uint8(e[159])) * 1000
            + uint256(uint8(e[223]));
    }

    // Ternary selecting between storage bytes INSIDE the literal.
    function encTernary(bool c) external returns (uint256) {
        b1 = hex"aa";
        b2 = hex"bbcc";
        bytes memory e = abi.encode([c ? b1 : b2, b2]);
        return e.length * 1000000 + uint256(uint8(e[128])) * 1000
            + uint256(uint8(e[192]));
    }

    // Emit with a storage-element array literal argument.
    function emitBytes() external returns (uint256) {
        b1 = hex"aa";
        b2 = hex"bbcc";
        emit EBytes([b1, b2]);
        return 1;
    }

    // Custom-error revert carrying the storage-element array literal.
    function revertArr() external {
        b1 = hex"aa";
        b2 = hex"bbcc";
        revert EArr([b1, b2]);
    }
}
