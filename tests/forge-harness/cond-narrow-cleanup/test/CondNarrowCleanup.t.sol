// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CondNarrowCleanupHarnessTarget} from "../src/CondNarrowCleanup.sol";

contract CondNarrowCleanupForgeTest {
    CondNarrowCleanupHarnessTarget private t = new CondNarrowCleanupHarnessTarget();

    function expectPanic11(bytes memory callData, string memory label) internal {
        (bool ok, bytes memory ret) = address(t).call(callData);
        require(!ok, string.concat(label, ": expected revert"));
        require(ret.length == 36, string.concat(label, ": expected panic data"));
        bytes4 sel;
        uint256 code;
        assembly {
            sel := mload(add(ret, 32))
            code := mload(add(ret, 36))
        }
        require(sel == 0x4e487b71, string.concat(label, ": not Panic"));
        require(code == 0x11, string.concat(label, ": wrong code"));
    }

    function testWhileCondPanics() public {
        expectPanic11(abi.encodeCall(t.whileCond, (200, 100)), "whileCond");
    }
    function testForCondPanics() public {
        expectPanic11(abi.encodeCall(t.forCond, (200, 100)), "forCond");
    }
    function testDoWhileCondPanics() public {
        expectPanic11(abi.encodeCall(t.doWhileCond, (200, 100)), "doWhileCond");
    }
    function testPlainCmpPanics() public {
        expectPanic11(abi.encodeCall(t.plainCmp, (200, 100)), "plainCmp");
    }
    function testIfCondPanics() public {
        expectPanic11(abi.encodeCall(t.ifCond, (200, 100)), "ifCond");
    }
    function testRequireCondPanics() public {
        expectPanic11(abi.encodeCall(t.requireCond, (200, 100)), "requireCond");
    }
    function testAssertCondPanics() public {
        expectPanic11(abi.encodeCall(t.assertCond, (200, 100)), "assertCond");
    }
    function testExprStmtPanics() public {
        expectPanic11(abi.encodeCall(t.exprStmt, (200, 100)), "exprStmt");
    }
    function testEqCmpPanics() public {
        expectPanic11(abi.encodeCall(t.eqCmp, (200, 100)), "eqCmp");
    }
    function testIntWhileCondPanics() public {
        expectPanic11(abi.encodeCall(t.intWhileCond, (-100, -50)), "intWhileCond");
    }
    function testWhileCondSafe() public view {
        require(t.whileCondSafe(3, 4) == 3, "whileCondSafe: 3..6 then 7<10 fails at k=4? recompute");
    }
    function testPlainCmpSafe() public view {
        require(t.plainCmpSafe(3, 4) == true, "plainCmpSafe");
    }
    function testUncheckedCmpWraps() public view {
        require(t.uncheckedCmp(200, 100) == true, "uncheckedCmp: 44<250");
    }
    function testUncheckedWhileWraps() public view {
        require(t.uncheckedWhile(200, 100) == 3, "uncheckedWhile: wraps to 44, loops to k=3");
    }
    function testCastCmpTruncates() public view {
        require(t.castCmp(300) == true, "castCmp: 44<250");
    }
    function testIfAndCondPanics() public {
        expectPanic11(abi.encodeCall(t.ifAndCond, (200, 100)), "ifAndCond");
    }
    function testIfNotCondPanics() public {
        expectPanic11(abi.encodeCall(t.ifNotCond, (200, 100)), "ifNotCond");
    }
    function testIdxKeyPanics() public {
        expectPanic11(abi.encodeCall(t.idxKey, (200, 100)), "idxKey");
    }
    function testCallArgPanics() public {
        expectPanic11(abi.encodeCall(t.callArg, (200, 100)), "callArg");
    }
    function testWhileAndCondPanics() public {
        expectPanic11(abi.encodeCall(t.whileAndCond, (200, 100)), "whileAndCond");
    }
    function testIdxKeySafe() public view {
        require(t.idxKey(40, 4) == 9, "idxKey safe");
    }
    function testCallArgSafe() public view {
        require(t.callArg(40, 4) == 44, "callArg safe");
    }
}
