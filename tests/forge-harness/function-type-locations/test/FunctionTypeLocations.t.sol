// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/FunctionTypeLocations.sol";

contract FunctionTypeLocationsForgeTest {
    FunctionTypeLocations private target;

    function setUp() public {
        target = new FunctionTypeLocations();
    }

    function testInternalFunctionReferenceLocations() public {
        uint256[] memory values = new uint256[](2);
        values[0] = 4;
        values[1] = 5;

        (uint256 memoryValue, uint256 memoryResult) = target.runMemory(values);
        require(memoryValue == 5 && memoryResult == 5, "memory pointer");

        (uint256 calldataValue, uint256 calldataLength) = target.runCalldata(values);
        require(calldataValue == 4 && calldataLength == 2, "calldata pointer");

        (uint256 storageValue, uint256 storageResult) = target.runStorage();
        require(storageValue == 8 && storageResult == 8, "storage pointer");
    }
}
