// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/MappingIndex.sol";

contract MappingIndexForgeTest {
    function testWriteReadAndPublicGetter() public {
        MappingIndexHarnessTarget target = new MappingIndexHarnessTarget();

        require(target.writeRead(7, 33) == 33, "writeRead");
        require(target.values(7) == 33, "getter");
        require(target.values(8) == 0, "default");
        require(target.readDefault(8) == 0, "readDefault");
    }

    function testSeparateKeys() public {
        MappingIndexHarnessTarget target = new MappingIndexHarnessTarget();

        require(target.writeTwo(1, 2) == 33, "writeTwo");
        require(target.values(1) == 11, "first");
        require(target.values(2) == 22, "second");
    }

    function testAddressMapping() public {
        MappingIndexHarnessTarget target = new MappingIndexHarnessTarget();
        address who = address(0x1234);

        require(target.writeAddress(who, 44) == 44, "writeAddress");
        require(target.balances(who) == 44, "balance");
        require(target.balances(address(0x9999)) == 0, "other");
    }
}
