// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// #178 ENUM-MEMBER-ENCODEPACKED: an enum member-access literal (E.C) passed to
// abi.encodePacked must pack to its 1-byte underlying width (uint8), NOT the
// full 32-byte word. Ground truth: solc 0.8.35 legacy + real EVM.
contract EnumMemberEncodePacked {
    enum E { A, B, C, D }

    // abi.encodePacked(E.C) == 0x02 (one byte).
    function packMember() external pure returns (bytes memory) {
        return abi.encodePacked(E.C);
    }

    // Mixed: uint8(1), E.C, uint8(9) == 0x010209 (three bytes).
    function packMixed() external pure returns (bytes memory) {
        return abi.encodePacked(uint8(1), E.C, uint8(9));
    }

    // Constant-context regression guard: an enum member in a constant
    // initializer must still fold and accept.
    uint8 constant X = uint8(E.C);
    function constFold() external pure returns (uint8) {
        return X;
    }
}
