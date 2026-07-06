// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/OverrideDataLocations.sol";

contract OverrideDataLocationsForgeTest {
    OverrideDataLocations private target;

    function setUp() public {
        uint256[] memory initial = new uint256[](1);
        initial[0] = 5;
        target = new OverrideDataLocations(initial);
    }

    function testOverrideLocationBoundaries() public view {
        uint256[] memory values = new uint256[](2);
        values[0] = 17;
        values[1] = 23;

        require(target.publicMemory(values)[0] == 17, "public memory");
        require(target.publicCalldata(values)[1] == 23, "public calldata");
        require(target.externalMemory(values)[0] == 17, "external calldata");
        require(target.externalCalldata(values)[1] == 23, "external memory");
    }

    function testFreeFunctionReferenceBoundaries() public {
        uint256[] memory values = new uint256[](2);
        values[0] = 17;
        values[1] = 23;

        require(target.freeMemoryRoundTrip(values)[0] == 31, "free memory");
        require(target.freeCalldataRoundTrip(values)[1] == 23, "free calldata");

        (uint256 length, uint256 first, uint256 second) =
            target.freeStorageRoundTrip();
        require(length == 2, "free storage length");
        require(first == 9, "free storage first");
        require(second == 6, "free storage second");
    }
}
