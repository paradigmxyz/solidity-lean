// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LibStorageReturnUseHarness} from "../src/LibStorageReturnUse.sol";

contract LibStorageReturnUseForgeTest {
    LibStorageReturnUseHarness private harness = new LibStorageReturnUseHarness();

    // Write 42 through the value-returned storage ref, read it back through it.
    function testWriteReadStructThroughInternalStorageReturn() public {
        require(harness.writeReadStruct(42) == 42, "internal storage-return use roundtrip");
    }

    // Same via separate set/get calls, exercising persisted state.
    function testSetThenGetThroughInternalStorageReturn() public {
        harness.setThrough(42);
        require(harness.getThrough() == 42, "internal storage-return use set/get");
    }
}
