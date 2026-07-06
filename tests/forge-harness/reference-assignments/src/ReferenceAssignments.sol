// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReferenceAssignments {
    struct Pair {
        uint256 x;
        uint256 y;
    }

    struct Blob {
        bytes data;
        uint256 tag;
    }

    struct Bucket {
        uint256[] values;
    }

    uint256[] private stored;
    uint256[] private other;
    uint128[2] private fixedStored;
    uint128[2] private fixedOther;
    uint128[] private packedStored;
    uint256[][] private nestedStored;
    Bucket[] private bucketList;
    Pair private storedPair;
    bytes private storedBytes;
    bytes private otherBytes;
    string private storedString;
    string private otherString;
    Blob private storedBlob;
    Blob private otherBlob;
    Blob[] private blobList;
    Blob[] private otherBlobList;

    function memoryAlias(uint256[] memory input)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory localRef = input;
        localRef[0] = 7;
        return (input[0], localRef[0]);
    }

    function nestedMemoryArrayAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[][] memory matrix = new uint256[][](1);
        matrix[0] = new uint256[](1);
        matrix[0][0] = 1;
        uint256[][] memory localRef = matrix;
        localRef[0][0] = 42;
        return (matrix[0][0], localRef[0][0]);
    }

    function nestedMemoryArrayPathAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[][] memory matrix = new uint256[][](1);
        matrix[0] = new uint256[](1);
        matrix[0][0] = 1;
        uint256[] memory row = matrix[0];
        row[0] = 42;
        return (matrix[0][0], row[0]);
    }

    function calldataToMemoryCopy(uint256[] calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory copied = input;
        copied[0] = 7;
        return (input[0], copied[0]);
    }

    function calldataStructArrayToMemoryCopy(Blob[] calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        Blob[] memory copied = input;
        copied[0].data[0] = bytes1(uint8(7));
        copied[1].tag = 99;
        return (uint8(input[0].data[0]) + input[1].tag,
            uint8(copied[0].data[0]) + copied[1].tag);
    }

    function storageAlias() external returns (uint256, uint256) {
        delete stored;
        stored.push(1);
        uint256[] storage localRef = stored;
        localRef[0] = 7;
        return (stored[0], localRef[0]);
    }

    function storageToMemoryCopy() external returns (uint256, uint256) {
        delete stored;
        stored.push(1);
        uint256[] memory copied = stored;
        copied[0] = 7;
        return (stored[0], copied[0]);
    }

    function storageToStorageCopy() external returns (uint256, uint256) {
        delete stored;
        delete other;
        stored.push(1);
        other = stored;
        other[0] = 7;
        return (stored[0], other[0]);
    }

    function storageRefToMemoryCopy() external returns (uint256, uint256) {
        delete stored;
        stored.push(1);
        uint256[] storage localRef = stored;
        uint256[] memory copied = localRef;
        copied[0] = 7;
        return (localRef[0], copied[0]);
    }

    function storageRefLength() external returns (uint256, uint256) {
        delete stored;
        stored.push(1);
        stored.push(2);
        uint256[] storage localRef = stored;
        return (localRef.length, localRef[0]);
    }

    function fixedStorageToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        fixedStored[0] = 1;
        fixedStored[1] = 2;
        uint128[2] memory copied = fixedStored;
        copied[0] = 7;
        return (fixedStored[0], copied[0]);
    }

    function fixedStorageToStorageCopy()
        external
        returns (uint256, uint256)
    {
        fixedStored[0] = 1;
        fixedStored[1] = 2;
        fixedOther = fixedStored;
        fixedOther[0] = 7;
        return (fixedStored[0], fixedOther[0]);
    }

    function packedStorageToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        delete packedStored;
        packedStored.push(1);
        packedStored.push(2);
        uint128[] memory copied = packedStored;
        copied[0] = 7;
        return (packedStored[0], copied[0]);
    }

    function nestedStorageToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        delete nestedStored;
        nestedStored.push();
        nestedStored[0].push(1);
        uint256[][] memory copied = nestedStored;
        copied[0][0] = 7;
        return (nestedStored[0][0], copied[0][0]);
    }

    function storageStructArrayToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        delete blobList;
        blobList.push();
        blobList[0].data = hex"0102";
        blobList[0].tag = 3;
        blobList.push();
        blobList[1].data = hex"0304";
        blobList[1].tag = 4;
        Blob[] memory copied = blobList;
        copied[0].data[0] = bytes1(uint8(7));
        copied[1].tag = 99;
        return (uint8(blobList[0].data[0]) + blobList[1].tag,
            uint8(copied[0].data[0]) + copied[1].tag);
    }

    function storageStructArrayToStorageCopy()
        external
        returns (uint256, uint256)
    {
        delete blobList;
        delete otherBlobList;
        blobList.push();
        blobList[0].data = hex"0102";
        blobList[0].tag = 3;
        blobList.push();
        blobList[1].data = hex"0304";
        blobList[1].tag = 4;
        otherBlobList = blobList;
        otherBlobList[0].data[0] = bytes1(uint8(7));
        otherBlobList[1].tag = 99;
        return (uint8(blobList[0].data[0]) + blobList[1].tag,
            uint8(otherBlobList[0].data[0]) + otherBlobList[1].tag);
    }

    function storageStructArrayAliasNestedBytes()
        external
        returns (uint256, uint256)
    {
        delete blobList;
        blobList.push();
        blobList[0].data = hex"0102";
        blobList[0].tag = 3;
        blobList.push();
        blobList[1].data = hex"0304";
        blobList[1].tag = 4;
        Blob[] storage localRef = blobList;
        localRef[0].data[0] = bytes1(uint8(7));
        localRef[1].tag = 99;
        return (uint8(blobList[0].data[0]) + blobList[1].tag,
            uint8(localRef[0].data[0]) + localRef[1].tag);
    }

    function storageNestedArrayPushRef()
        external
        returns (uint256, uint256, uint256)
    {
        delete nestedStored;
        uint256[] storage row = nestedStored.push();
        row.push(31);
        uint256[] storage same = nestedStored[0];
        same[0] = 32;
        return (nestedStored.length, nestedStored[0].length, row[0]);
    }

    function storageStructArrayPushRef()
        external
        returns (uint256, uint256, uint256)
    {
        delete bucketList;
        Bucket storage bucket = bucketList.push();
        bucket.values.push(41);
        Bucket storage same = bucketList[0];
        same.values[0] = 42;
        return (bucketList.length, bucket.values.length, bucketList[0].values[0]);
    }

    function storageNestedArrayPopClearsElement()
        external
        returns (uint256, uint256, uint256)
    {
        delete nestedStored;
        nestedStored.push();
        nestedStored[0].push(11);
        nestedStored.pop();
        nestedStored.push();
        uint256 lengthAfterReuse = nestedStored.length;
        uint256 rowLengthBeforePush = nestedStored[0].length;
        nestedStored[0].push(12);
        return (lengthAfterReuse, rowLengthBeforePush, nestedStored[0][0]);
    }

    function storageStructArrayPopClearsElement()
        external
        returns (uint256, uint256, uint256)
    {
        delete bucketList;
        bucketList.push();
        bucketList[0].values.push(21);
        bucketList.pop();
        bucketList.push();
        uint256 lengthAfterReuse = bucketList.length;
        uint256 valuesLengthBeforePush = bucketList[0].values.length;
        bucketList[0].values.push(22);
        return (lengthAfterReuse, valuesLengthBeforePush, bucketList[0].values[0]);
    }

    function storageNestedArrayDeleteClearsElement()
        external
        returns (uint256, uint256, uint256)
    {
        delete nestedStored;
        nestedStored.push();
        nestedStored[0].push(13);
        delete nestedStored;
        nestedStored.push();
        uint256 lengthAfterReuse = nestedStored.length;
        uint256 rowLengthBeforePush = nestedStored[0].length;
        nestedStored[0].push(14);
        return (lengthAfterReuse, rowLengthBeforePush, nestedStored[0][0]);
    }

    function storageStructArrayDeleteClearsElement()
        external
        returns (uint256, uint256, uint256)
    {
        delete bucketList;
        bucketList.push();
        bucketList[0].values.push(23);
        delete bucketList;
        bucketList.push();
        uint256 lengthAfterReuse = bucketList.length;
        uint256 valuesLengthBeforePush = bucketList[0].values.length;
        bucketList[0].values.push(24);
        return (lengthAfterReuse, valuesLengthBeforePush, bucketList[0].values[0]);
    }

    function storageStructDeleteClearsDynamicField()
        external
        returns (uint256, uint256, uint256)
    {
        storedBlob = Blob({data: hex"0102", tag: 7});
        delete storedBlob;
        uint256 dataLengthBeforePush = storedBlob.data.length;
        storedBlob.data.push(bytes1(uint8(32)));
        return (dataLengthBeforePush, uint8(storedBlob.data[0]), storedBlob.tag);
    }

    function memoryToStorageCopy(uint256[] memory input)
        external
        returns (uint256, uint256)
    {
        delete stored;
        stored = input;
        input[0] = 7;
        return (stored[0], input[0]);
    }

    function memoryStructAlias() external pure returns (uint256, uint256) {
        Pair memory first = Pair({x: 1, y: 2});
        Pair memory second = first;
        second.x = 7;
        return (first.x, second.x);
    }

    function memoryStructArrayFieldAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        Bucket memory bucket = Bucket({values: values});
        uint256[] memory localRef = bucket.values;
        localRef[0] = 77;
        return (bucket.values[0], localRef[0]);
    }

    function memoryStructWholeAssignArrayFieldAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        Bucket memory first = Bucket({values: values});
        Bucket memory second = first;
        second.values[0] = 88;
        return (first.values[0], second.values[0]);
    }

    function storageStructToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        storedPair = Pair({x: 1, y: 2});
        Pair memory copied = storedPair;
        copied.x = 7;
        return (storedPair.x, copied.x);
    }

    function memoryBytesAlias(bytes memory input)
        external
        pure
        returns (uint256, uint256)
    {
        bytes memory localRef = input;
        localRef[0] = bytes1(uint8(7));
        return (uint8(input[0]), uint8(localRef[0]));
    }

    function calldataBytesToMemoryCopy(bytes calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        bytes memory copied = input;
        copied[0] = bytes1(uint8(7));
        return (uint8(input[0]), uint8(copied[0]));
    }

    function storageBytesAlias() external returns (uint256, uint256) {
        storedBytes = hex"0102";
        bytes storage localRef = storedBytes;
        localRef[0] = bytes1(uint8(7));
        return (uint8(storedBytes[0]), uint8(localRef[0]));
    }

    function storageBytesToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        storedBytes = hex"0102";
        bytes memory copied = storedBytes;
        copied[0] = bytes1(uint8(7));
        return (uint8(storedBytes[0]), uint8(copied[0]));
    }

    function storageBytesToStorageCopy()
        external
        returns (uint256, uint256)
    {
        storedBytes = hex"0102";
        otherBytes = storedBytes;
        otherBytes[0] = bytes1(uint8(7));
        return (uint8(storedBytes[0]), uint8(otherBytes[0]));
    }

    function storageBytesPushPop()
        external
        returns (uint256, uint256)
    {
        delete storedBytes;
        storedBytes.push(bytes1(uint8(1)));
        storedBytes.push(bytes1(uint8(2)));
        storedBytes.pop();
        return (storedBytes.length, uint8(storedBytes[0]));
    }

    function storageStringToStorageCopy()
        external
        returns (uint256, uint256)
    {
        storedString = "ab";
        otherString = storedString;
        storedString = "z";
        return (bytes(storedString).length, bytes(otherString).length);
    }

    function nestedStorageBytesToMemoryCopy()
        external
        returns (uint256, uint256)
    {
        storedBlob = Blob({data: hex"0102", tag: 3});
        Blob memory copied = storedBlob;
        copied.data[0] = bytes1(uint8(7));
        return (uint8(storedBlob.data[0]), uint8(copied.data[0]));
    }

    function nestedStorageBytesToStorageCopy()
        external
        returns (uint256, uint256)
    {
        storedBlob = Blob({data: hex"0102", tag: 3});
        otherBlob = storedBlob;
        otherBlob.data[0] = bytes1(uint8(7));
        return (uint8(storedBlob.data[0]), uint8(otherBlob.data[0]));
    }

    function memoryStructNestedBytesAlias()
        external
        pure
        returns (uint256, uint256)
    {
        Blob memory first = Blob({data: hex"0102", tag: 3});
        Blob memory second = first;
        second.data[0] = bytes1(uint8(7));
        return (uint8(first.data[0]), uint8(second.data[0]));
    }

    function storageBytesLongToMemoryCopy(bytes calldata input)
        external
        returns (uint256, uint256)
    {
        storedBytes = input;
        bytes memory copied = storedBytes;
        copied[0] = bytes1(uint8(7));
        return (storedBytes.length, uint8(copied[0]));
    }

    function storageBytesShortLongTransition()
        external
        returns (uint256, uint256)
    {
        delete storedBytes;
        for (uint8 i = 1; i <= 33; i++) {
            storedBytes.push(bytes1(i));
        }
        storedBytes.pop();
        storedBytes.pop();
        return (storedBytes.length, uint8(storedBytes[30]));
    }

    function storageStringLongCopy(string calldata input)
        external
        returns (uint256, uint256)
    {
        storedString = input;
        otherString = storedString;
        storedString = "z";
        return (bytes(storedString).length, bytes(otherString).length);
    }

    function storageBytesPopEmpty() external {
        delete storedBytes;
        storedBytes.pop();
    }

    function storageBytesPushAssign()
        external
        returns (uint256, uint256)
    {
        delete storedBytes;
        storedBytes.push() = bytes1(uint8(9));
        return (storedBytes.length, uint8(storedBytes[0]));
    }

    function nestedStorageBytesPushAssign()
        external
        returns (uint256, uint256)
    {
        delete storedBlob;
        storedBlob.data.push() = bytes1(uint8(9));
        return (storedBlob.data.length, uint8(storedBlob.data[0]));
    }
}
