// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {BytesNIdentIndexHarnessTarget} from "../src/BytesNIdentIndex.sol";

contract BytesNIdentIndexForgeTest {
    bytes32 constant V =
        0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff;
    bytes4 constant V4 = 0xaabbccdd;

    function newTarget() internal returns (BytesNIdentIndexHarnessTarget) {
        return new BytesNIdentIndexHarnessTarget();
    }

    // A reverting call must Panic with array-out-of-bounds (0x32).
    function expectPanic32(bytes memory reason) internal pure {
        require(reason.length == 36, "not a Panic payload");
        require(bytes4(reason) == bytes4(0x4e487b71), "not Panic selector");
        uint256 code;
        assembly { code := mload(add(reason, 0x24)) }
        require(code == 0x32, "not array-out-of-bounds");
    }

    // #175 PARAM bytes32.
    function testParam0() public { require(newTarget().fParam(V, 0) == bytes1(0x00), "p0"); }
    function testParam3() public { require(newTarget().fParam(V, 3) == bytes1(0x33), "p3"); }
    function testParam31() public { require(newTarget().fParam(V, 31) == bytes1(0xff), "p31"); }
    function testParamOOB() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        try t.fParam(V, 32) returns (bytes1) { revert("expected revert"); }
        catch (bytes memory reason) { expectPanic32(reason); }
    }

    // #175 PARAM bytes4.
    function testParam4_0() public { require(newTarget().fParam4(V4, 0) == bytes1(0xaa), "p4_0"); }
    function testParam4_1() public { require(newTarget().fParam4(V4, 1) == bytes1(0xbb), "p4_1"); }
    function testParam4OOB() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        try t.fParam4(V4, 4) returns (bytes1) { revert("expected revert"); }
        catch (bytes memory reason) { expectPanic32(reason); }
    }

    // #175 LOCAL bytes32.
    function testLocal3() public { require(newTarget().fLocal(3) == bytes1(0x33), "l3"); }
    function testLocalOOB() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        try t.fLocal(32) returns (bytes1) { revert("expected revert"); }
        catch (bytes memory reason) { expectPanic32(reason); }
    }

    // #176 STATE VAR bytes32.
    function testState0() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB(V);
        require(t.getByte(0) == bytes1(0x00), "s0");
    }
    function testState3() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB(V);
        require(t.getByte(3) == bytes1(0x33), "s3");
    }
    function testState31() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB(V);
        require(t.getByte(31) == bytes1(0xff), "s31");
    }
    function testStateOOB() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB(V);
        try t.getByte(32) returns (bytes1) { revert("expected revert"); }
        catch (bytes memory reason) { expectPanic32(reason); }
    }

    // #176 STATE VAR bytes4.
    function testState4_0() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB4(V4);
        require(t.getByte4(0) == bytes1(0xaa), "s4_0");
    }
    function testState4OOB() public {
        BytesNIdentIndexHarnessTarget t = newTarget();
        t.setB4(V4);
        try t.getByte4(4) returns (bytes1) { revert("expected revert"); }
        catch (bytes memory reason) { expectPanic32(reason); }
    }
}
