// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {AggregateContractMemberHarnessTarget, IThing} from "../src/AggregateContractMember.sol";

interface Vm {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

contract AggregateContractMemberForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testContractTypedMemberLayout() public {
        AggregateContractMemberHarnessTarget target =
            new AggregateContractMemberHarnessTarget();
        require(target.setAll() == 0x9999, "set");

        (
            uint96 u,
            address c,
            uint8 z,
            address st,
            uint256 sx,
            uint256 afterS,
            uint256 mv
        ) = target.readAll();
        require(u == 0xABCD, "u");
        require(c == address(0xAA), "c");
        require(z == 0x77, "z");
        require(st == address(0xBB), "s.t");
        require(sx == 0x1234, "s.x");
        require(afterS == 0x9999, "afterS");
        require(mv == 0x555, "mc value");

        // (a) contract var packs: slot0 = u (low 12 bytes) | c (20 bytes at off 12).
        bytes32 slot0 = vm.load(address(target), bytes32(uint256(0)));
        require(slot0 == bytes32((uint256(0xAA) << 96) | uint256(0xABCD)), "slot0 packed");
        // z sits in slot 1 (only reachable because c packed into slot 0).
        require(uint256(vm.load(address(target), bytes32(uint256(1)))) == 0x77, "z slot1");

        // (b) struct with a contract field spans 2 slots: t@2, x@3, afterS@4.
        require(uint256(vm.load(address(target), bytes32(uint256(2)))) == 0xBB, "s.t slot2");
        require(uint256(vm.load(address(target), bytes32(uint256(3)))) == 0x1234, "s.x slot3");
        require(uint256(vm.load(address(target), bytes32(uint256(4)))) == 0x9999, "afterS slot4");

        // (c) mapping(IThing => uint) hashes the key as keccak256(pad32(addr) . slot5).
        bytes32 mcSlot = keccak256(abi.encode(uint256(uint160(address(0xCC))), uint256(5)));
        require(uint256(vm.load(address(target), mcSlot)) == 0x555, "mc keccak slot");
    }
}
