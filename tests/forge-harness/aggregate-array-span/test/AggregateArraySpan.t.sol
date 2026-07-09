// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {AggregateArraySpanHarnessTarget} from "../src/AggregateArraySpan.sol";

interface Vm {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

contract AggregateArraySpanForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testFixedArraySpanNoStraddle() public {
        AggregateArraySpanHarnessTarget target = new AggregateArraySpanHarnessTarget();
        require(target.setAll() == 0x99, "set");

        (uint256 head, uint40 e0, uint40 e31, uint8 tail1) = target.readAll();
        require(head == 1, "head");
        require(e0 == 0xaa, "f1[0]");
        require(e31 == 0xbb, "f1[31]");
        require(tail1 == 0x99, "tail1");

        // uint40[32] spans 6 slots (floor(32/5)=6 per slot, ceil(32/6)=6), so the
        // trailing scalar lands at slot 7 (a straddling 5-slot span would put it at 6).
        require(uint256(vm.load(address(target), bytes32(uint256(0)))) == 1, "head slot0");
        require(uint256(vm.load(address(target), bytes32(uint256(7)))) == 0x99, "tail1 slot7");
        // f1[31] sits in slot 6 at byte offset (31%6)*5 = 5.
        uint256 slot6 = uint256(vm.load(address(target), bytes32(uint256(6))));
        require((slot6 >> 40) & 0xffffffffff == 0xbb, "f1[31] in slot6 off5");
    }
}
