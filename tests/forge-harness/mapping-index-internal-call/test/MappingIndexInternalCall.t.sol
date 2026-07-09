// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {MappingIndexInternalCallHarnessTarget} from "../src/MappingIndexInternalCall.sol";

contract MappingIndexInternalCallForgeTest {
    function testMappingIndex() public {
        MappingIndexInternalCallHarnessTarget t = new MappingIndexInternalCallHarnessTarget();
        require(t.runMapping(9, 123) == 123, "runMapping");
        require(t.readMapping(9) == 123, "readMapping");
        require(t.readMapping(8) == 0, "default");
    }

    function testNarrowValue() public {
        MappingIndexInternalCallHarnessTarget t = new MappingIndexInternalCallHarnessTarget();
        require(t.runNarrow(3, 250) == 250, "runNarrow");
    }

    function testArrayIndex() public {
        MappingIndexInternalCallHarnessTarget t = new MappingIndexInternalCallHarnessTarget();
        require(t.runArray(0, 44) == 44, "runArray0");
        MappingIndexInternalCallHarnessTarget t2 = new MappingIndexInternalCallHarnessTarget();
        require(t2.runArray(3, 77) == 77, "runArray3");
    }

    function testEvalOrderRhsBeforeIndex() public {
        MappingIndexInternalCallHarnessTarget t = new MappingIndexInternalCallHarnessTarget();
        // solc evaluates the RHS (log+100 == 100) before the LHS index bump():
        // m[0] is stored as 100 (index-first would be 105).
        require(t.runOrder() == 100, "order");
    }
}
