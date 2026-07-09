// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {AggregateBytesNMappingKeyHarnessTarget} from "../src/AggregateBytesNMappingKey.sol";

interface Vm {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

contract AggregateBytesNMappingKeyForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testBytesNKeyLeftAligned() public {
        AggregateBytesNMappingKeyHarnessTarget target =
            new AggregateBytesNMappingKeyHarnessTarget();
        require(target.setKeys() == 111, "set");

        (uint256 a, uint256 b, uint256 c) = target.readKeys();
        require(a == 111 && b == 222 && c == 333, "roundtrip");

        // bytes4 key is hashed LEFT-aligned: preimage word = bytes32(bytes4(key)).
        bytes32 leftSlot = keccak256(abi.encode(bytes32(bytes4(0xaabbccdd)), uint256(0)));
        require(uint256(vm.load(address(target), leftSlot)) == 111, "b4 left slot");

        // The right-aligned preimage (the pre-fix Solidus slot) must read zero.
        bytes32 rightSlot = keccak256(abi.encode(uint256(0xaabbccdd), uint256(0)));
        require(uint256(vm.load(address(target), rightSlot)) == 0, "b4 right slot empty");

        // uint32 value-key control: right-aligned, base slot 1.
        bytes32 ctrlSlot = keccak256(abi.encode(uint256(0xaabbccdd), uint256(1)));
        require(uint256(vm.load(address(target), ctrlSlot)) == 222, "u32 ctrl slot");

        // Nested: outer key uint256(7) at base 2, inner bytes4 left-aligned.
        bytes32 outer = keccak256(abi.encode(uint256(7), uint256(2)));
        bytes32 innerSlot = keccak256(abi.encode(bytes32(bytes4(0xaabbccdd)), outer));
        require(uint256(vm.load(address(target), innerSlot)) == 333, "nested inner slot");
    }
}
