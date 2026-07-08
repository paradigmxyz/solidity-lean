// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {MemoryAllocationOverflow} from "../src/MemoryAllocationOverflow.sol";

contract MemoryAllocationOverflowForgeTest {
    function panicCode(bytes memory data) internal pure returns (uint256) {
        require(data.length == 36, "not a panic payload");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(data, 0x20))
            code := mload(add(data, 0x24))
        }
        require(selector == bytes4(0x4e487b71), "not panic selector");
        return code;
    }

    function expectPanic41(bytes memory callData) internal {
        MemoryAllocationOverflow target = new MemoryAllocationOverflow();
        (bool ok, bytes memory data) = address(target).staticcall(callData);
        require(!ok, "expected revert");
        require(panicCode(data) == 0x41, "expected Panic 0x41");
    }

    function testAllocBytesMaxPanics41() public {
        expectPanic41(
            abi.encodeWithSignature("allocBytes(uint256)", type(uint256).max)
        );
    }

    function testAllocBytesJustOverThresholdPanics41() public {
        expectPanic41(
            abi.encodeWithSignature("allocBytes(uint256)", uint256(1) << 64)
        );
    }

    function testAllocArrayMaxPanics41() public {
        expectPanic41(
            abi.encodeWithSignature("allocArray(uint256)", type(uint256).max)
        );
    }

    function testAllocArrayJustOverThresholdPanics41() public {
        expectPanic41(
            abi.encodeWithSignature("allocArray(uint256)", uint256(1) << 64)
        );
    }

    function testAllocSmallSucceeds() public {
        MemoryAllocationOverflow target = new MemoryAllocationOverflow();
        require(target.allocBytes(3) == 3, "small bytes length");
        require(target.allocArray(3) == 3, "small array length");
    }
}
