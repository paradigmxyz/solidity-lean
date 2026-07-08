// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    Dl1LinC,
    Dl1DiaG,
    Dl1ShZ
} from "../src/StorageOrderLinearization.sol";

interface Vm {
    function load(address target, bytes32 slot) external view returns (bytes32);
}

contract StorageOrderLinearizationForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _slot(address target, uint256 slot) private view returns (uint256) {
        return uint256(vm.load(target, bytes32(slot)));
    }

    // Linear control: DFS and reverse-C3 coincide; unaffected by the fix.
    function testLinearControl() public {
        Dl1LinC t = new Dl1LinC();
        // constructor order Root,A,B,C -> trace 123
        require(t.trace() == 123, "lin trace");
        require(t.a() == 11 && t.b() == 22 && t.c() == 33, "lin getters");
        // storage: trace@0, a@1, b@2, c@3
        require(_slot(address(t), 0) == 123, "lin slot0");
        require(_slot(address(t), 1) == 11, "lin slot1");
        require(_slot(address(t), 2) == 22, "lin slot2");
        require(_slot(address(t), 3) == 33, "lin slot3");
    }

    // Simple diamond control: DFS and reverse-C3 coincide; unaffected by the fix.
    function testDiamondControl() public {
        Dl1DiaG t = new Dl1DiaG();
        // constructor order Root,D,E,F,G -> trace 4567
        require(t.trace() == 4567, "dia trace");
        require(t.d() == 44 && t.e() == 55 && t.f() == 66 && t.g() == 77, "dia getters");
        // storage: trace@0, d@1, e@2, f@3, g@4
        require(_slot(address(t), 0) == 4567, "dia slot0");
        require(_slot(address(t), 1) == 44, "dia slot1");
        require(_slot(address(t), 2) == 55, "dia slot2");
        require(_slot(address(t), 3) == 66, "dia slot3");
        require(_slot(address(t), 4) == 77, "dia slot4");
    }

    // DL1: shared direct+indirect base. Buggy DFS gave trace 2134 and sx/sy
    // slots swapped; reverse-C3 gives trace 1234 and sx@1, sy@2.
    function testSharedBaseLinearization() public {
        Dl1ShZ t = new Dl1ShZ();
        // constructor order Root,X,Y,M,Z -> trace 1234
        require(t.trace() == 1234, "shared trace");
        require(t.sx() == 111 && t.sy() == 222 && t.sm() == 333 && t.sz() == 444, "shared getters");
        // storage: trace@0, sx@1, sy@2, sm@3, sz@4
        require(_slot(address(t), 0) == 1234, "shared slot0");
        require(_slot(address(t), 1) == 111, "shared slot1 sx");
        require(_slot(address(t), 2) == 222, "shared slot2 sy");
        require(_slot(address(t), 3) == 333, "shared slot3 sm");
        require(_slot(address(t), 4) == 444, "shared slot4 sz");
    }
}
