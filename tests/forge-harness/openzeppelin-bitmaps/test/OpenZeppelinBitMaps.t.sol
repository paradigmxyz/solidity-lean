// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OpenZeppelinBitMapsHarness} from "../src/OpenZeppelinBitMaps.sol";

contract OpenZeppelinBitMapsForgeTest {
    function testSetUnsetAndPackedBuckets() public {
        OpenZeppelinBitMapsHarness target =
            new OpenZeppelinBitMapsHarness();

        require(!target.get(0), "initial zero");
        require(target.set(0), "set zero");
        require(target.get(0), "get zero");
        require(target.bucket(0) == 1, "bucket zero");

        require(target.set(1), "set one");
        require(target.bucket(0) == 3, "bucket one");

        require(target.set(255), "set high bit");
        require(target.bucket(0) == ((uint256(1) << 255) | 3), "bucket high");

        require(target.set(256), "set next bucket");
        require(target.bucket(1) == 1, "bucket one start");
        require(target.bucket(0) == ((uint256(1) << 255) | 3), "bucket keep");

        require(!target.unset(1), "unset one");
        require(!target.get(1), "get unset one");
        require(target.bucket(0) == ((uint256(1) << 255) | 1), "bucket unset");
    }

    function testSetToAndBucketMasks() public {
        OpenZeppelinBitMapsHarness target =
            new OpenZeppelinBitMapsHarness();

        require(target.setTo(300, true), "set 300");
        require(target.bucket(1) == (uint256(1) << 44), "bucket 300");
        require(!target.setTo(300, false), "unset 300");
        require(target.bucket(1) == 0, "clear 300");

        require(target.setTo(511, true), "set 511");
        require(target.bucket(1) == (uint256(1) << 255), "bucket 511");
    }

    function testDuplicateSetAndIndependentBuckets() public {
        OpenZeppelinBitMapsHarness target =
            new OpenZeppelinBitMapsHarness();

        require(target.setPair(0, 0) == 1, "duplicate set");
        require(target.bucket(0) == 1, "duplicate bucket");
        require(target.set(512), "set bucket two");
        require(target.bucket(2) == 1, "bucket two");
        require(target.bucket(0) == 1, "bucket zero unchanged");
    }
}
