// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import {BuiltinArgResidue} from "../src/BuiltinArgResidue.sol";

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

contract BuiltinArgResidueForgeTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
    bytes constant PANIC11 = abi.encodeWithSignature("Panic(uint256)", 0x11);

    BuiltinArgResidue p;

    function setUp() public { p = new BuiltinArgResidue(); }

    // controls
    function test_ctrlReturn() public { vm.expectRevert(PANIC11); p.ctrlReturn(200, 100); }
    function test_ctrlStmt() public { vm.expectRevert(PANIC11); p.ctrlStmt(200, 100); }
    function test_ctrlSafe() public view {
        require(
            keccak256(p.ctrlSafe(3, 4)) == keccak256(abi.encode(uint8(7))),
            "ctrlSafe value");
    }

    // A. assignment RHS
    function test_asgLocal() public { vm.expectRevert(PANIC11); p.asgLocal(200, 100); }
    function test_asgHash() public { vm.expectRevert(PANIC11); p.asgHash(200, 100); }
    function test_asgConcat() public { vm.expectRevert(PANIC11); p.asgConcat(200, 100); }
    function test_asgStorage() public { vm.expectRevert(PANIC11); p.asgStorage(200, 100); }

    // B. vardecl init
    function test_vdBytes() public { vm.expectRevert(PANIC11); p.vdBytes(200, 100); }
    function test_vdHash() public { vm.expectRevert(PANIC11); p.vdHash(200, 100); }
    function test_vdNested() public { vm.expectRevert(PANIC11); p.vdNested(200, 100); }

    // C. require / assert condition
    function test_reqHash() public { vm.expectRevert(PANIC11); p.reqHash(200, 100, bytes32(0)); }
    function test_reqEnc() public { vm.expectRevert(PANIC11); p.reqEnc(200, 100); }
    function test_assertHash() public { vm.expectRevert(PANIC11); p.assertHash(200, 100, bytes32(0)); }

    // D. emit args
    function test_emitEnc() public { vm.expectRevert(PANIC11); p.emitEnc(200, 100); }
    function test_emitHash() public { vm.expectRevert(PANIC11); p.emitHash(200, 100); }

    // E. revert custom-error arg (panic replaces the custom revert data)
    function test_revErr() public { vm.expectRevert(PANIC11); p.revErr(200, 100); }

    // controls: function-call arg (Stage-D green)
    function test_callEnc() public { vm.expectRevert(PANIC11); p.callEnc(200, 100); }
    function test_callHash() public { vm.expectRevert(PANIC11); p.callHash(200, 100); }

    // F. nested builtin-in-builtin
    function test_nestConcat() public { vm.expectRevert(PANIC11); p.nestConcat(200, 100); }
    function test_nestEnc() public { vm.expectRevert(PANIC11); p.nestEnc(200, 100); }

    // D. emit mixed pure+call: the panic fires BEFORE bump() so cnt stays 0
    function test_emitMix() public {
        vm.expectRevert(PANIC11);
        p.emitMix(200, 100);
        require(p.cnt() == 0, "bump must not run");
    }
    function test_emitMixSafe() public {
        p.emitMix(3, 4);
        require(p.cnt() == 1, "safe emitMix bumps once");
    }

    // control: pure-then-call emit arg order (data [0, 1])
    function test_emitOrder() public {
        vm.recordLogs();
        p.emitOrder();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one event");
        (uint256 x, uint256 y) = abi.decode(logs[0].data, (uint256, uint256));
        require(x == 0 && y == 1, "EO logs [0, 1]");
    }

    // G. lvalue index-key residue
    function test_lvStruct() public { vm.expectRevert(PANIC11); p.lvStruct(200, 100, 7); }
    function test_lvMapDeep() public { vm.expectRevert(PANIC11); p.lvMapDeep(200, 100, 1, 7); }
    function test_lvCompound() public { vm.expectRevert(PANIC11); p.lvCompound(200, 100); }
    function test_lvDelete() public { vm.expectRevert(PANIC11); p.lvDelete(200, 100); }

    // G. no-write checks: the failed compound/delete never touched arr[300]
    function test_lvCompoundNoWrite() public {
        vm.expectRevert(PANIC11);
        p.lvCompound(200, 100);
        require(p.arr(300) == 300, "arr[300] untouched");
    }
    function test_lvDeleteNoWrite() public {
        vm.expectRevert(PANIC11);
        p.lvDelete(200, 100);
        require(p.arr(300) == 300, "arr[300] untouched");
    }
}
