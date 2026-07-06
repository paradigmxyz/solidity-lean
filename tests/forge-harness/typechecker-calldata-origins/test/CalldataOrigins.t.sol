// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/CalldataOrigins.sol";

contract CalldataOriginsForgeTest {
    function values(uint256 first) internal pure returns (uint256[] memory out) {
        out = new uint256[](2);
        out[0] = first;
        out[1] = first + 1;
    }

    function testCalldataAliasesAndCopies() public {
        CalldataOrigins target = new CalldataOrigins();
        uint256[] memory first = values(3);
        uint256[] memory second = values(7);

        (uint256 localLength, uint256 localFirst) = target.localAlias(first);
        require(localLength == 2 && localFirst == 3, "local alias");

        uint256[] memory returned = target.returnAlias(first);
        require(returned.length == 2 && returned[0] == 3, "return alias");
        require(target.internalAlias(first) == 2, "internal alias");

        (uint256 original, uint256 copied) = target.calldataToMemory(first);
        require(original == 3 && copied == 9, "memory copy");

        (uint256 before, uint256 afterValue) =
            target.reassignAlias(first, second);
        require(before == 3 && afterValue == 7, "reassignment");

        (uint256 tupleLeft, uint256 tupleRight) =
            target.tupleAlias(first, second);
        require(tupleLeft == 3 && tupleRight == 7, "tuple alias");
    }

    function testAbiBoundariesAcceptMemory() public {
        CalldataOrigins target = new CalldataOrigins();
        uint256[] memory input = values(11);

        require(target.memoryToExternal(input) == 2, "external ABI");
        require(
            target.memoryToPublicLibrary(input) == 2,
            "library ABI"
        );
        require(
            target.memoryToUsingPublicLibrary(input) == 2,
            "using ABI"
        );
        require(
            target.calldataToInternalLibrary(input) == 2,
            "internal library"
        );
    }
}
