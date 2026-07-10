// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {TupleWriteOrderHarnessTarget} from "../src/TupleWriteOrder.sol";

contract TupleWriteOrderForgeTest {
    function testLocalAliasLeftmostWins() public {
        TupleWriteOrderHarnessTarget t = new TupleWriteOrderHarnessTarget();
        // (x, x) = (1, 2): leftmost wins → 1.
        require(t.runLocalAlias() == 1, "local alias");
    }

    function testStorageAliasLeftmostWins() public {
        TupleWriteOrderHarnessTarget t = new TupleWriteOrderHarnessTarget();
        // (arr[0], arr[0]) = (1, 2): leftmost wins → arr[0] == 1.
        require(t.runStorageAlias() == 1, "storage alias ret");
        require(t.getArr(0) == 1, "storage alias arr0");
    }

    function testIndexObservesPreStoreState() public {
        TupleWriteOrderHarnessTarget t = new TupleWriteOrderHarnessTarget();
        // arr[0]=5; (arr[0], arr[arr[0]]) = (1, 2): second index sees arr[0]==5
        // → writes arr[5]=2; then arr[0]=1. Packed 1*100 + 0*10 + 2 == 102.
        require(t.runIndexPreStore() == 102, "prestore packed");
        require(t.getArr(0) == 1, "prestore arr0");
        require(t.getArr(1) == 0, "prestore arr1");
        require(t.getArr(5) == 2, "prestore arr5");
    }
}
