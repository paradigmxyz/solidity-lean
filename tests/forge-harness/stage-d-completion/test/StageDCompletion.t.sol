// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import {StageDCompletion} from "../src/StageDCompletion.sol";

interface Vm {
    function expectRevert(bytes calldata) external;
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory);
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }
}

contract StageDCompletionForgeTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    bytes constant PANIC11 = abi.encodeWithSignature("Panic(uint256)", 0x11);

    StageDCompletion c;

    function setUp() public {
        c = new StageDCompletion();
    }

    // ---- #193 divergent cases now Panic 0x11 ----
    function test_h1_panics() public { vm.expectRevert(PANIC11); c.h1(200, 100); }
    function test_h2_panics() public { vm.expectRevert(PANIC11); c.h2(200, 100); }
    function test_h3_panics() public { vm.expectRevert(PANIC11); c.h3(200, 100); }
    function test_h4_panics() public { vm.expectRevert(PANIC11); c.h4(100, 100); }
    function test_h5_panics() public { vm.expectRevert(PANIC11); c.h5(-128); }

    // ---- #193 controls ----
    function test_c1_panics() public { vm.expectRevert(PANIC11); c.c1(200, 100); }
    function test_c2_panics() public {
        vm.expectRevert(PANIC11);
        c.c2(type(uint256).max, 5);
    }
    function test_c3_panics() public { vm.expectRevert(PANIC11); c.c3(3, 5); }
    function test_hSafe() public view {
        require(c.hSafe(3, 4) == keccak256(abi.encodePacked(uint8(7))), "hSafe");
    }

    // ---- #194 write cases Panic 0x11 (and do NOT write) ----
    function test_w1_panics() public { vm.expectRevert(PANIC11); c.w1(200, 100); }
    function test_w2_panics() public { vm.expectRevert(PANIC11); c.w2(200, 100); }
    function test_w3_panics() public { vm.expectRevert(PANIC11); c.w3(200, 100); }
    function test_w4_panics() public { vm.expectRevert(PANIC11); c.w4(200, 100); }
    function test_rRead_panics() public { vm.expectRevert(PANIC11); c.rRead(200, 100); }
    function test_wSafe() public {
        require(c.wSafe(3, 4) == 7, "wSafe");
    }

    // ---- #195 emit two-phase order ----
    function test_emit2() public {
        vm.recordLogs();
        uint256 tr = c.emit2();
        require(tr == 211, "emit2 trace");
        Vm.Log[] memory logs = vm.getRecordedLogs();
        // E2(x, indexed y, z): topic[1] = y, data = (x, z)
        require(logs[0].topics[1] == bytes32(uint256(2)), "emit2 topic y");
        (uint256 x, uint256 z) = abi.decode(logs[0].data, (uint256, uint256));
        require(x == 21, "emit2 x");
        require(z == 211, "emit2 z");
    }
    function test_emit3() public {
        vm.recordLogs();
        uint256 tr = c.emit3();
        require(tr == 21, "emit3 trace");
        Vm.Log[] memory logs = vm.getRecordedLogs();
        // E3(indexed x, indexed y): topic[1] = x, topic[2] = y
        require(logs[0].topics[1] == bytes32(uint256(21)), "emit3 x");
        require(logs[0].topics[2] == bytes32(uint256(2)), "emit3 y");
    }
    // #195 control: all-non-indexed stays L2R
    function test_emitData() public {
        vm.recordLogs();
        uint256 tr = c.emitData();
        require(tr == 12, "emitData trace");
        Vm.Log[] memory logs = vm.getRecordedLogs();
        (uint256 x, uint256 y) = abi.decode(logs[0].data, (uint256, uint256));
        require(x == 1, "emitData x");
        require(y == 12, "emitData y");
    }
}
