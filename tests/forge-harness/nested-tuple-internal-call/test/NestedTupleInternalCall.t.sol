// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NestedTupleInternalCallHarnessTarget} from "../src/NestedTupleInternalCall.sol";

contract NestedTupleInternalCallForgeTest {
    function testFlatMulti() public {
        NestedTupleInternalCallHarnessTarget t = new NestedTupleInternalCallHarnessTarget();
        require(t.flatMulti() == 10203012, "flatMulti");
    }
    function testNestedCalls() public {
        NestedTupleInternalCallHarnessTarget t = new NestedTupleInternalCallHarnessTarget();
        require(t.nestedCalls() == 102030345, "nestedCalls");
    }
    function testNestedHole() public {
        NestedTupleInternalCallHarnessTarget t = new NestedTupleInternalCallHarnessTarget();
        require(t.nestedHole() == 4099967, "nestedHole");
    }
}
