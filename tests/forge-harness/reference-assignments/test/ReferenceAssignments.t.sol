// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReferenceAssignments.sol";

contract ReferenceAssignmentsForgeTest {
    function values() internal pure returns (uint256[] memory result) {
        result = new uint256[](2);
        result[0] = 1;
        result[1] = 2;
    }

    function checkPair(
        uint256 actualX,
        uint256 actualY,
        uint256 expectedX,
        uint256 expectedY
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
    }

    function checkTriple(
        uint256 actualX,
        uint256 actualY,
        uint256 actualZ,
        uint256 expectedX,
        uint256 expectedY,
        uint256 expectedZ
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
        require(actualZ == expectedZ, "third");
    }

    function testMemoryAndCalldataAssignments() public {
        ReferenceAssignments target = new ReferenceAssignments();
        uint256[] memory input = values();

        (uint256 memoryX, uint256 memoryY) = target.memoryAlias(input);
        checkPair(memoryX, memoryY, 7, 7);

        input = values();
        (uint256 calldataX, uint256 calldataY) =
            target.calldataToMemoryCopy(input);
        checkPair(calldataX, calldataY, 1, 7);

        ReferenceAssignments.Blob[] memory blobs =
            new ReferenceAssignments.Blob[](2);
        blobs[0] = ReferenceAssignments.Blob({data: hex"0102", tag: 3});
        blobs[1] = ReferenceAssignments.Blob({data: hex"0304", tag: 4});
        (uint256 originalSum, uint256 copiedSum) =
            target.calldataStructArrayToMemoryCopy(blobs);
        checkPair(originalSum, copiedSum, 5, 106);
    }

    function testNestedMemoryAliases() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 nestedX, uint256 nestedY) =
            target.nestedMemoryArrayAlias();
        checkPair(nestedX, nestedY, 42, 42);

        (uint256 pathX, uint256 pathY) =
            target.nestedMemoryArrayPathAlias();
        checkPair(pathX, pathY, 42, 42);

        (uint256 fieldX, uint256 fieldY) =
            target.memoryStructArrayFieldAlias();
        checkPair(fieldX, fieldY, 77, 77);

        (uint256 wholeX, uint256 wholeY) =
            target.memoryStructWholeAssignArrayFieldAlias();
        checkPair(wholeX, wholeY, 88, 88);
    }

    function testStorageArrayAssignments() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 aliasX, uint256 aliasY) = target.storageAlias();
        checkPair(aliasX, aliasY, 7, 7);

        (uint256 toMemoryX, uint256 toMemoryY) =
            target.storageToMemoryCopy();
        checkPair(toMemoryX, toMemoryY, 1, 7);

        (uint256 toStorageX, uint256 toStorageY) =
            target.storageToStorageCopy();
        checkPair(toStorageX, toStorageY, 1, 7);

        (uint256 refToMemoryX, uint256 refToMemoryY) =
            target.storageRefToMemoryCopy();
        checkPair(refToMemoryX, refToMemoryY, 1, 7);

        (uint256 refLength, uint256 refFirst) = target.storageRefLength();
        checkPair(refLength, refFirst, 2, 1);
    }

    function testStorageArrayLayoutCopies() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 fixedToMemoryX, uint256 fixedToMemoryY) =
            target.fixedStorageToMemoryCopy();
        checkPair(fixedToMemoryX, fixedToMemoryY, 1, 7);

        (uint256 fixedToStorageX, uint256 fixedToStorageY) =
            target.fixedStorageToStorageCopy();
        checkPair(fixedToStorageX, fixedToStorageY, 1, 7);

        (uint256 packedX, uint256 packedY) =
            target.packedStorageToMemoryCopy();
        checkPair(packedX, packedY, 1, 7);

        (uint256 nestedX, uint256 nestedY) =
            target.nestedStorageToMemoryCopy();
        checkPair(nestedX, nestedY, 1, 7);

        (uint256 storageStructArrayX, uint256 storageStructArrayY) =
            target.storageStructArrayToMemoryCopy();
        checkPair(storageStructArrayX, storageStructArrayY, 5, 106);

        (uint256 storageStructArrayStorageX, uint256 storageStructArrayStorageY) =
            target.storageStructArrayToStorageCopy();
        checkPair(storageStructArrayStorageX, storageStructArrayStorageY, 5, 106);

        (uint256 storageStructArrayAliasX, uint256 storageStructArrayAliasY) =
            target.storageStructArrayAliasNestedBytes();
        checkPair(storageStructArrayAliasX, storageStructArrayAliasY, 106, 106);
    }

    function testStoragePushReturnReferences() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 nestedLength, uint256 rowLength, uint256 rowFirst) =
            target.storageNestedArrayPushRef();
        checkTriple(nestedLength, rowLength, rowFirst, 1, 1, 32);

        (uint256 bucketLength, uint256 valuesLength, uint256 valuesFirst) =
            target.storageStructArrayPushRef();
        checkTriple(bucketLength, valuesLength, valuesFirst, 1, 1, 42);

        (
            uint256 nestedPopLength,
            uint256 nestedPopRowLength,
            uint256 nestedPopFirst
        ) = target.storageNestedArrayPopClearsElement();
        checkTriple(nestedPopLength, nestedPopRowLength, nestedPopFirst, 1, 0, 12);

        (
            uint256 bucketPopLength,
            uint256 bucketPopValuesLength,
            uint256 bucketPopFirst
        ) = target.storageStructArrayPopClearsElement();
        checkTriple(bucketPopLength, bucketPopValuesLength, bucketPopFirst, 1, 0, 22);
    }

    function testStorageDeleteDeepClears() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (
            uint256 nestedDeleteLength,
            uint256 nestedDeleteRowLength,
            uint256 nestedDeleteFirst
        ) = target.storageNestedArrayDeleteClearsElement();
        checkTriple(
            nestedDeleteLength,
            nestedDeleteRowLength,
            nestedDeleteFirst,
            1,
            0,
            14
        );

        (
            uint256 bucketDeleteLength,
            uint256 bucketDeleteValuesLength,
            uint256 bucketDeleteFirst
        ) = target.storageStructArrayDeleteClearsElement();
        checkTriple(
            bucketDeleteLength,
            bucketDeleteValuesLength,
            bucketDeleteFirst,
            1,
            0,
            24
        );

        (
            uint256 blobDataLength,
            uint256 blobDataFirst,
            uint256 blobTag
        ) = target.storageStructDeleteClearsDynamicField();
        checkTriple(blobDataLength, blobDataFirst, blobTag, 0, 32, 0);
    }

    function testMemoryToStorageCopy() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 storedX, uint256 memoryX) =
            target.memoryToStorageCopy(values());
        checkPair(storedX, memoryX, 1, 7);
    }

    function testStructAssignments() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 memoryX, uint256 memoryY) = target.memoryStructAlias();
        checkPair(memoryX, memoryY, 7, 7);

        (uint256 storageX, uint256 copiedX) =
            target.storageStructToMemoryCopy();
        checkPair(storageX, copiedX, 1, 7);
    }

    function testBytesAssignmentsAndMutation() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 memoryX, uint256 memoryY) =
            target.memoryBytesAlias(hex"0102");
        checkPair(memoryX, memoryY, 7, 7);

        (uint256 calldataX, uint256 calldataY) =
            target.calldataBytesToMemoryCopy(hex"0102");
        checkPair(calldataX, calldataY, 1, 7);

        (uint256 aliasX, uint256 aliasY) = target.storageBytesAlias();
        checkPair(aliasX, aliasY, 7, 7);

        (uint256 toMemoryX, uint256 toMemoryY) =
            target.storageBytesToMemoryCopy();
        checkPair(toMemoryX, toMemoryY, 1, 7);

        (uint256 toStorageX, uint256 toStorageY) =
            target.storageBytesToStorageCopy();
        checkPair(toStorageX, toStorageY, 1, 7);

        (uint256 length, uint256 first) = target.storageBytesPushPop();
        checkPair(length, first, 1, 1);
    }

    function testStringAndNestedBytesAssignments() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 stringX, uint256 stringY) =
            target.storageStringToStorageCopy();
        checkPair(stringX, stringY, 1, 2);

        (uint256 toMemoryX, uint256 toMemoryY) =
            target.nestedStorageBytesToMemoryCopy();
        checkPair(toMemoryX, toMemoryY, 1, 7);

        (uint256 toStorageX, uint256 toStorageY) =
            target.nestedStorageBytesToStorageCopy();
        checkPair(toStorageX, toStorageY, 1, 7);

        (uint256 aliasX, uint256 aliasY) =
            target.memoryStructNestedBytesAlias();
        checkPair(aliasX, aliasY, 7, 7);
    }

    function testLongBytesAndStringStorageBoundaries() public {
        ReferenceAssignments target = new ReferenceAssignments();
        bytes memory longBytes = new bytes(40);
        for (uint256 i = 0; i < longBytes.length; i++) {
            longBytes[i] = bytes1(uint8(i + 1));
        }

        (uint256 longLength, uint256 copiedFirst) =
            target.storageBytesLongToMemoryCopy(longBytes);
        checkPair(longLength, copiedFirst, 40, 7);

        (uint256 shortLength, uint256 shortLast) =
            target.storageBytesShortLongTransition();
        checkPair(shortLength, shortLast, 31, 31);

        (uint256 currentStringLength, uint256 copiedStringLength) =
            target.storageStringLongCopy(
                "0123456789012345678901234567890123456789"
            );
        checkPair(currentStringLength, copiedStringLength, 1, 40);
    }

    function testStorageBytesPopEmptyPanic() public {
        ReferenceAssignments target = new ReferenceAssignments();
        try target.storageBytesPopEmpty() {
            revert("expected panic");
        } catch Panic(uint256 code) {
            require(code == 0x31, "panic code");
        }
    }

    function testStorageBytesPushAssignment() public {
        ReferenceAssignments target = new ReferenceAssignments();

        (uint256 directLength, uint256 directFirst) =
            target.storageBytesPushAssign();
        checkPair(directLength, directFirst, 1, 9);

        (uint256 nestedLength, uint256 nestedFirst) =
            target.nestedStorageBytesPushAssign();
        checkPair(nestedLength, nestedFirst, 1, 9);
    }
}
