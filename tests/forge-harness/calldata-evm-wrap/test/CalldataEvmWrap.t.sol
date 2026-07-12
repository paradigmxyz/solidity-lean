// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/CalldataEvmWrap.sol";

// Real-EVM ground truth for #129: nested calldata dynamic-element tail access
// wraps mod 2^256 (signed slt + add). All calldata is hand-built via
// abi.encodePacked + low-level staticcall (the ordinary encoder never emits a
// high-bit tail offset). Layout for firstElem(bytes[]):
//   [0:4]   selector
//   [4:36]  offset_a  (relative to headStart=4)
//   ...     a's tail: [len][elem0 rel_offset][...]
// arrayPos (= base_ref) is right after the array length word.
contract CalldataEvmWrapForgeTest {
    CalldataEvmWrapTarget private target;

    function setUp() public {
        target = new CalldataEvmWrapTarget();
    }

    function _abiBytes(bytes memory data) internal pure returns (bytes memory) {
        // ABI encoding of a single `bytes` return: offset 0x20, length, data.
        return abi.encode(data);
    }

    // WRAP SUCCESS: elem0 rel_offset = 2^256-128 (signed -128). base_ref=164,
    // csz=196 -> slt(-128, 196-164-31=1)=true; addr=164-128=36; bytes at 36 has
    // length 2, data 0xaabb. EVM returns 0xaabb.
    function testWrapSuccessReturnsAabb() public {
        bytes memory cd = abi.encodePacked(
            CalldataEvmWrapTarget.firstElem.selector,
            uint256(0x80),                              // offset_a = 128 -> tail at [132]
            uint256(0x02),                              // [36:68]  target bytes length = 2
            bytes32(0xaabb000000000000000000000000000000000000000000000000000000000000), // [68:100] data
            uint256(0x00),                              // [100:132] pad
            uint256(0x01),                              // [132:164] array length = 1
            bytes32(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80)  // [164:196] elem0 rel_offset = -128
        );
        (bool ok, bytes memory ret) = address(target).staticcall(cd);
        require(ok, "wrap-success must succeed");
        require(keccak256(ret) == keccak256(_abiBytes(hex"aabb")), "wrap-success must return 0xaabb");
    }

    // WRAP FAR: elem0 rel_offset = 2^255 (most negative). slt passes; addr huge;
    // calldataload zero-pads -> length 0; signed sgt sees negative addr -> no
    // revert. EVM returns EMPTY bytes.
    function testWrapFarReturnsEmpty() public {
        bytes memory cd = abi.encodePacked(
            CalldataEvmWrapTarget.firstElem.selector,
            uint256(0x80),
            uint256(0x02),
            bytes32(0xaabb000000000000000000000000000000000000000000000000000000000000),
            uint256(0x00),
            uint256(0x01),
            bytes32(0x8000000000000000000000000000000000000000000000000000000000000000)
        );
        (bool ok, bytes memory ret) = address(target).staticcall(cd);
        require(ok, "wrap-far must succeed");
        require(keccak256(ret) == keccak256(_abiBytes(hex"")), "wrap-far must return empty bytes");
    }

    // POSITIVE OOB (regression armor): elem0 rel_offset = 0x1000 (positive, past
    // calldatasize). slt fails -> EMPTY revert. This is the boundary the wrap
    // must NOT erase.
    function testPositiveOobReverts() public {
        bytes memory cd = abi.encodePacked(
            CalldataEvmWrapTarget.firstElem.selector,
            uint256(0x80),
            uint256(0x02),
            bytes32(0xaabb000000000000000000000000000000000000000000000000000000000000),
            uint256(0x00),
            uint256(0x01),
            bytes32(uint256(0x1000))
        );
        (bool ok, bytes memory ret) = address(target).staticcall(cd);
        require(!ok, "positive-OOB tail offset must revert");
        require(ret.length == 0, "positive-OOB reverts empty");
    }

    // NORMAL FORWARD (control): elem0 rel_offset = 0x20 (small, in-bounds). No
    // wrap. EVM returns 0xaabb.
    function testNormalForwardReturnsAabb() public {
        bytes memory cd = abi.encodePacked(
            CalldataEvmWrapTarget.firstElem.selector,
            uint256(0x20),   // offset_a=32 -> tail at [36]
            uint256(0x01),   // [36:68] length = 1
            uint256(0x20),   // [68:100] elem0 rel_offset = 0x20 -> addr = 68+32 = 100
            uint256(0x02),   // [100:132] bytes length = 2
            bytes32(0xaabb000000000000000000000000000000000000000000000000000000000000) // [132:164] data
        );
        (bool ok, bytes memory ret) = address(target).staticcall(cd);
        require(ok, "normal-forward must succeed");
        require(keccak256(ret) == keccak256(_abiBytes(hex"aabb")), "normal-forward must return 0xaabb");
    }

    // LENGTH control: never follows a tail -> returns 1 regardless of offsets.
    function testLenControl() public {
        bytes memory cd = abi.encodePacked(
            CalldataEvmWrapTarget.len.selector,
            uint256(0x20),
            uint256(0x01),
            bytes32(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80)
        );
        (bool ok, bytes memory ret) = address(target).staticcall(cd);
        require(ok, "len must succeed");
        require(abi.decode(ret, (uint256)) == 1, "len must be 1");
    }
}
