// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/MemoryAllocation.sol";

contract MemoryAllocationForgeTest {
    function testDynamicArrayAllocation() public {
        MemoryAllocation target = new MemoryAllocation();
        (uint256 length, uint256 first, uint256 middle, uint256 last) =
            target.allocate(3);
        require(length == 3, "length");
        require(first == 0, "first");
        require(middle == 7, "middle");
        require(last == 0, "last");
    }

    function testBytesAllocation() public {
        MemoryAllocation target = new MemoryAllocation();
        (
            bytes memory data,
            uint256 length,
            uint256 first,
            uint256 middle,
            uint256 last
        ) = target.allocateBytes(3);
        require(data.length == 3, "data length");
        require(data[0] == bytes1(uint8(0)), "data first");
        require(data[1] == bytes1(uint8(0xab)), "data middle");
        require(data[2] == bytes1(uint8(0)), "data last");
        require(length == 3, "length");
        require(first == 0, "first");
        require(middle == 0xab, "middle");
        require(last == 0, "last");
    }

    function testStringAllocation() public {
        MemoryAllocation target = new MemoryAllocation();
        (string memory text, uint256 length) = target.allocateString(3);
        bytes memory data = bytes(text);
        require(data.length == 3, "data length");
        require(data[0] == bytes1(uint8(0)), "data first");
        require(data[1] == bytes1(uint8(0)), "data middle");
        require(data[2] == bytes1(uint8(0)), "data last");
        require(length == 3, "length");
    }

    function testNestedArrayDefaults() public {
        MemoryAllocation target = new MemoryAllocation();
        (uint256 outerLength, uint256 defaultFirst, uint256 updatedSecond) =
            target.nestedArrayDefaults();
        require(outerLength == 2, "outer length");
        require(defaultFirst == 0, "default first");
        require(updatedSecond == 9, "updated second");
    }
}
