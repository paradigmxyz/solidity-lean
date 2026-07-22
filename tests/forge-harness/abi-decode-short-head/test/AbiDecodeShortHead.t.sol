// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/AbiDecodeShortHead.sol";

contract AbiDecodeShortHeadForgeTest {
    AbiDecodeShortHeadHarnessTarget private target;

    function setUp() public {
        target = new AbiDecodeShortHeadHarnessTarget();
    }

    // 63 bytes for a 64-byte head: upfront slt check -> EMPTY revert
    // (success == false, returndata length 0), NOT Panic(0x41).
    function testDecodeShortEmptyRevert() public {
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature("decodeShort()")
        );
        require(!ok, "short-head decode should revert");
        require(ret.length == 0, "short-head returndata must be empty");
    }

    // Control: a well-formed encoding still decodes.
    function testDecodeControl() public view {
        (uint256 sum, uint256 b) = target.decodeControl();
        require(sum == 16, "control sum");
        require(b == 5, "control b");
    }

    // Nested-struct short head: EMPTY revert at the struct-frame head check.
    function testDecodeNestedShortEmptyRevert() public {
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature("decodeNestedShort()")
        );
        require(!ok, "nested short-head decode should revert");
        require(ret.length == 0, "nested short-head returndata must be empty");
    }
}
