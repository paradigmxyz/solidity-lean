// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReferenceInternalMemoryBoundaries {
    struct Bucket {
        uint256[] values;
    }

    function mutateMemoryParam(uint256[] memory input) internal pure {
        input[0] = 91;
    }

    function returnMemoryParam(uint256[] memory input)
        internal
        pure
        returns (uint256[] memory)
    {
        return input;
    }

    function returnMemoryParamTwice(uint256[] memory input)
        internal
        pure
        returns (uint256[] memory, uint256[] memory)
    {
        return (input, input);
    }

    function returnMemoryBucket(Bucket memory bucket)
        internal
        pure
        returns (Bucket memory)
    {
        return bucket;
    }

    function mutateMemoryBytes(bytes memory input) internal pure {
        input[0] = bytes1(uint8(17));
    }

    function returnMemoryBytes(bytes memory input)
        internal
        pure
        returns (bytes memory)
    {
        return input;
    }

    function internalMemoryParamAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        mutateMemoryParam(values);
        return (values[0], 91);
    }

    function internalMemoryReturnAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        uint256[] memory localRef = returnMemoryParam(values);
        localRef[0] = 92;
        return (values[0], localRef[0]);
    }

    function internalMemoryTupleReturnAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        (uint256[] memory first, uint256[] memory second) =
            returnMemoryParamTwice(values);
        first[0] = 93;
        return (values[0], second[0]);
    }

    function internalMemoryStructReturnAlias()
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory values = new uint256[](1);
        values[0] = 1;
        Bucket memory bucket = Bucket({values: values});
        Bucket memory localRef = returnMemoryBucket(bucket);
        localRef.values[0] = 94;
        return (bucket.values[0], localRef.values[0]);
    }

    function internalBytesParamAlias()
        external
        pure
        returns (uint256, uint256)
    {
        bytes memory data = hex"0102";
        mutateMemoryBytes(data);
        return (uint8(data[0]), 17);
    }

    function internalBytesReturnAlias()
        external
        pure
        returns (uint256, uint256)
    {
        bytes memory data = hex"0102";
        bytes memory localRef = returnMemoryBytes(data);
        localRef[0] = bytes1(uint8(18));
        return (uint8(data[0]), uint8(localRef[0]));
    }
}
