// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import {AuditProbe} from "../src/AuditProbe.sol";

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

contract AuditProbeForgeTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    bytes constant PANIC11 = abi.encodeWithSignature("Panic(uint256)", 0x11);

    AuditProbe p;

    function setUp() public { p = new AuditProbe(); }

    function test_emitNamed() public { vm.expectRevert(PANIC11); p.emitNamed(200, 100); }
    function test_revNamed() public { vm.expectRevert(PANIC11); p.revNamed(200, 100); }
    function test_arrLit() public { vm.expectRevert(PANIC11); p.arrLit(200, 100); }
    function test_structCtor() public { vm.expectRevert(PANIC11); p.structCtor(200, 100); }
    function test_structNamed() public { vm.expectRevert(PANIC11); p.structNamed(200, 100); }
    function test_newSize() public { vm.expectRevert(PANIC11); p.newSize(200, 100); }
    function test_tupleAssign() public { vm.expectRevert(PANIC11); p.tupleAssign(200, 100); }
    function test_tupleDecl() public { vm.expectRevert(PANIC11); p.tupleDecl(200, 100); }
    function test_extArg() public { vm.expectRevert(PANIC11); p.extArg(200, 100); }
    function test_tryArg() public { vm.expectRevert(PANIC11); p.tryArg(200, 100); }
    function test_libArg() public { vm.expectRevert(PANIC11); p.libArg(200, 100); }
    function test_fnPtrArg() public { vm.expectRevert(PANIC11); p.fnPtrArg(200, 100); }
    function test_modArg() public { vm.expectRevert(PANIC11); p.modArg(200, 100); }
    function test_addmodArg() public { vm.expectRevert(PANIC11); p.addmodArg(200, 100); }
    function test_pushArg() public { vm.expectRevert(PANIC11); p.pushArg(200, 100); }
    function test_idxNested() public { vm.expectRevert(PANIC11); p.idxNested(200, 100); }
    function test_forInit() public { vm.expectRevert(PANIC11); p.forInit(200, 100); }
    function test_delMapKey() public { vm.expectRevert(PANIC11); p.delMapKey(200, 100); }
    function test_emitIndexed() public { vm.expectRevert(PANIC11); p.emitIndexed(200, 100); }
    function test_unchkVd() public view { require(p.unchkVd(200, 100) == 44, "wrap"); }
    function test_unchkTuple() public view { require(p.unchkTuple(200, 100) == 44, "wrapT"); }

    // safe-value controls
    function test_safe_tupleDecl() public view { require(p.tupleDecl(3, 4) == 7, "s1"); }
    function test_safe_arrLit() public view { require(p.arrLit(3, 4) == 7, "s2"); }
    function test_safe_newSize() public view { require(p.newSize(3, 4) == 7, "s3"); }
    function test_safe_libArg() public view { require(p.libArg(3, 4) == 7, "s4"); }
    function test_safe_usingArg() public view { require(p.usingArg(10, 4) == 27, "s5"); }

    // #196 chains
    function test_chain3() public view { require(p.chain3(10) == 27, "c3"); }
    function test_chain4() public view { require(p.chain4(10) == 32, "c4"); }
    function test_chain3lib() public view { require(p.chain3lib(10) == 27, "c3l"); }
    function test_chain3vd() public view { require(p.chain3vd(10) == 27, "c3v"); }
    function test_chain3emit() public {
        vm.recordLogs();
        p.chain3emit(10);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics[1] == bytes32(uint256(27)), "topic 27");
    }

    // two-phase indexed emit order: x=2, y=1
    function test_emit2Idx() public {
        vm.recordLogs();
        p.emit2Idx();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics[1] == bytes32(uint256(2)), "x=2");
        require(logs[0].topics[2] == bytes32(uint256(1)), "y=1");
    }
}
