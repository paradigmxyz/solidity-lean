// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReferenceMappingStorage.sol";

contract ReferenceMappingStorageForgeTest {
    function checkPair(
        uint256 actualX,
        uint256 actualY,
        uint256 expectedX,
        uint256 expectedY
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
    }

    function testMappingAliases() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (uint256 directX, uint256 directY) =
            target.mappingAlias(7, 33);
        checkPair(directX, directY, 33, 33);

        (uint256 nestedX, uint256 nestedY) =
            target.nestedMappingAlias(3, 9, 44);
        checkPair(nestedX, nestedY, 44, 44);
    }

    function testStructMappingAlias() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (uint256 total, uint256 viaState, uint256 viaAlias) =
            target.structMappingAlias(5, 8, 55, 77);

        require(total == 77, "total");
        require(viaState == 55, "state");
        require(viaAlias == 55, "alias");
    }

    function testDeleteStructKeepsMappingEntries() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (uint256 totalAfterDelete, uint256 creditAfterDelete) =
            target.deleteStructKeepsMapping(6, 10, 99, 123);

        checkPair(totalAfterDelete, creditAfterDelete, 0, 99);
    }

    function testStructReferenceRebind() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (
            uint256 firstCredit,
            uint256 secondTotal,
            uint256 secondCredit
        ) = target.structReferenceRebind(7, 8, 3, 21, 34, 55);

        require(firstCredit == 21, "first credit");
        require(secondTotal == 55, "second total");
        require(secondCredit == 35, "second credit");
    }

    function testDeleteArrayMappingValue() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (
            uint256 beforeLength,
            uint256 first,
            uint256 afterLength,
            uint256 neighborLength
        ) = target.deleteArrayValue(11);

        require(beforeLength == 2, "array before length");
        require(first == 11, "array first");
        require(afterLength == 0, "array after length");
        require(neighborLength == 1, "array neighbor length");
    }

    function testDeleteBytesMappingValue() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (
            uint256 beforeLength,
            uint256 second,
            uint256 afterLength,
            uint256 neighborLength
        ) = target.deleteBytesValue(13);

        require(beforeLength == 2, "bytes before length");
        require(second == 2, "bytes second");
        require(afterLength == 0, "bytes after length");
        require(neighborLength == 1, "bytes neighbor length");
    }

    function testDeleteStringMappingValue() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (
            string memory beforeDelete,
            string memory afterDelete,
            string memory neighbor
        ) = target.deleteStringValue(17);

        require(keccak256(bytes(beforeDelete)) == keccak256("abc"), "string before");
        require(bytes(afterDelete).length == 0, "string after");
        require(keccak256(bytes(neighbor)) == keccak256("z"), "string neighbor");
    }

    function testDeleteStructDynamicMappingValue() public {
        ReferenceMappingStorage target = new ReferenceMappingStorage();

        (
            uint256 beforeDelete,
            uint256 totalAfter,
            uint256 numbersAfter,
            uint256 rawAfter
        ) = target.deleteStructDynamicValue(19);

        require(beforeDelete == 80, "struct before");
        require(totalAfter == 0, "struct total after");
        require(numbersAfter == 0, "struct numbers after");
        require(rawAfter == 0, "struct raw after");
    }
}
