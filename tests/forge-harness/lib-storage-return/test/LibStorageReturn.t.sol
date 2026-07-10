// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {L} from "../src/LibStorageReturn.sol";

// Consumer that exercises the library storage-return headers at RUNTIME on the
// real EVM: it writes and reads state THROUGH the storage reference / mapping
// reference returned by the (public) library functions.
contract LibStorageReturnHarness {
    L.S internal s;
    L.D internal d;

    // Write x through the returned `S storage` ref, then read it back.
    function writeReadStruct() external returns (uint256) {
        L.refPublic(s).x = 42;
        return L.refPublic(s).x;
    }

    // Write a mapping entry through the returned `mapping storage` ref, read back.
    function writeReadMap() external returns (uint256) {
        L.mapPublic(d)[7] = 99;
        return L.mapPublic(d)[7];
    }
}

contract LibStorageReturnForgeTest {
    LibStorageReturnHarness private harness = new LibStorageReturnHarness();

    function testWriteReadStructThroughStorageReturn() public {
        require(harness.writeReadStruct() == 42, "struct storage return read/write");
    }

    function testWriteReadMapThroughStorageReturn() public {
        require(harness.writeReadMap() == 99, "mapping storage return read/write");
    }
}
