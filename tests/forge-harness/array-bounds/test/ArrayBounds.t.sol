// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/ArrayBounds.sol";

contract ArrayBoundsForgeTest {
    ArrayBoundsHarnessTarget private target;

    function setUp() public {
        target = new ArrayBoundsHarnessTarget();
    }

    // ARRAY-OOB-CONV: `a[uint256(5)]` compiles; the OOB read reverts with the
    // 36-byte Panic(0x32) returndata at runtime.
    function testConvOobPanic32() public {
        (bool ok, bytes memory ret) =
            address(target).call(abi.encodeWithSignature("convOob()"));
        require(!ok, "conv OOB should revert");
        require(ret.length == 36, "Panic(0x32) returndata length");
        require(
            keccak256(ret)
                == keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x32))),
            "conv OOB must be Panic(0x32)"
        );
    }

    // Control: in-bounds converted index returns the default element value.
    function testConvInBounds() public view {
        require(target.convInBounds() == 0, "in-bounds conv value");
    }

    // SLICE-FIXED: dynamic calldata array slice is accepted and returns length.
    function testDynSliceLength() public view {
        uint256[] memory xs = new uint256[](4);
        xs[0] = 10;
        xs[1] = 20;
        xs[2] = 30;
        xs[3] = 40;
        require(target.dynSlice(xs) == 2, "dynamic slice length");
    }
}
