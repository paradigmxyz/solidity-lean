// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {StorageBytesEncoding} from "../src/StorageBytesEncoding.sol";

interface VmStore {
    function store(address target, bytes32 slot, bytes32 value) external;
}

contract StorageBytesEncodingForgeTest {
    VmStore internal constant vm =
        VmStore(address(uint160(uint256(keccak256("hevm cheat code")))));

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

    function expectPanic22(address target, bytes memory callData)
        internal
        view
    {
        (bool ok, bytes memory data) = target.staticcall(callData);
        require(!ok, "expected revert");
        require(panicCode(data) == 0x22, "expected Panic 0x22");
    }

    // Long form (low bit set) with encoded length 16 (< 32): word = 16*2+1 = 33.
    function testDirtyBytesLongFormShortLengthPanics22() public {
        StorageBytesEncoding target = new StorageBytesEncoding();
        vm.store(address(target), bytes32(uint256(0)), bytes32(uint256(33)));
        expectPanic22(
            address(target), abi.encodeWithSignature("dataLength()")
        );
        expectPanic22(address(target), abi.encodeWithSignature("data()"));
        expectPanic22(
            address(target), abi.encodeWithSignature("readData()")
        );
    }

    function testDirtyStringLongFormShortLengthPanics22() public {
        StorageBytesEncoding target = new StorageBytesEncoding();
        vm.store(address(target), bytes32(uint256(1)), bytes32(uint256(33)));
        expectPanic22(
            address(target), abi.encodeWithSignature("textLength()")
        );
    }

    // Long form with encoded length exactly 32 is well-formed: word = 32*2+1 = 65.
    function testLongFormLength32IsValid() public {
        StorageBytesEncoding target = new StorageBytesEncoding();
        vm.store(address(target), bytes32(uint256(0)), bytes32(uint256(65)));
        require(target.dataLength() == 32, "length 32 valid");
    }
}
