// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface AbiMalformedNarrowReturn {
    function narrowValue() external returns (uint8);
}

interface AbiMalformedBoolReturn {
    function boolValue() external returns (bool);
}

interface AbiMalformedAddressReturn {
    function addressValue() external returns (address);
}

interface AbiMalformedFixedBytesReturn {
    function fixedBytesValue() external returns (bytes4);
}

interface AbiMalformedIgnoredAddressReturn {
    function pairValue() external returns (uint256, address);
}

interface AbiMalformedIgnoredFixedBytesReturn {
    function pairValue() external returns (uint256, bytes4);
}

interface AbiMalformedBytesReturn {
    function bytesValue() external returns (bytes memory);
}

interface AbiMalformedUint8ArrayReturn {
    function uint8ArrayValue() external returns (uint8[] memory);
}

interface AbiMalformedUint8FixedArrayReturn {
    function uint8FixedArrayValue() external returns (uint8[2] memory);
}

enum AbiMalformedChoice {
    Zero,
    One
}

struct AbiMalformedConstructorPair {
    uint8 clean;
    uint8 dirty;
}

interface AbiMalformedEnumReturn {
    function enumValue() external returns (AbiMalformedChoice);
}

contract AbiMalformedReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return abi.encode(uint256(256));
    }
}

contract AbiMalformedBoolReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return abi.encode(uint256(2));
    }
}

contract AbiMalformedAddressReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return abi.encode(uint256(1) << 160);
    }
}

contract AbiMalformedFixedBytesReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(hex"01020304", bytes28(uint224(1)));
    }
}

contract AbiMalformedIgnoredAddressReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(bytes32(uint256(7)), bytes32(uint256(1) << 160));
    }
}

contract AbiMalformedIgnoredFixedBytesReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(
            bytes32(uint256(7)),
            hex"01020304",
            bytes28(uint224(1))
        );
    }
}

contract AbiMalformedBytesReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(bytes32(uint256(32)), bytes32(uint256(1)), "a");
    }
}

contract AbiMalformedArrayReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(
            bytes32(uint256(32)),
            bytes32(uint256(1)),
            bytes32(uint256(256))
        );
    }
}

contract AbiMalformedFixedArrayReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(bytes32(uint256(7)), bytes32(uint256(256)));
    }
}

contract AbiMalformedEnumReturnTarget {
    fallback(bytes calldata) external returns (bytes memory) {
        return abi.encode(uint256(2));
    }
}

contract AbiMalformedConstructorArrayLength {
    uint256 public observed;

    constructor(uint8[] memory input) {
        observed = input.length;
    }
}

contract AbiMalformedConstructorFixedArrayFirst {
    uint256 public observed;

    constructor(uint8[2] memory input) {
        observed = input[0];
    }
}

contract AbiMalformedConstructorPairFirst {
    uint256 public observed;

    constructor(AbiMalformedConstructorPair memory input) {
        observed = input.clean;
    }
}

contract AbiMalformed {
    struct NarrowPair {
        uint8 clean;
        uint8 dirty;
    }

    struct DynBytesPair {
        uint256 clean;
        bytes dirty;
    }

    mapping(uint8 => uint256) public narrowMap;

    constructor(uint8 seed) {
        narrowMap[seed] = seed;
    }

    function bytesLength(bytes calldata input)
        external
        pure
        returns (uint256)
    {
        return input.length;
    }

    function decodeBytes(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        bytes memory decoded = abi.decode(encoded, (bytes));
        return decoded.length;
    }

    function addressValue(address input) external pure returns (uint256) {
        return uint160(input);
    }

    function addressUnused(address) external pure returns (uint256) {
        return 1;
    }

    function fixedBytesValue(bytes4 input) external pure returns (bytes4) {
        return input;
    }

    function fixedBytesUnused(bytes4) external pure returns (uint256) {
        return 1;
    }

    function boolValue(bool input) external pure returns (uint256) {
        return input ? 1 : 0;
    }

    function boolUnused(bool) external pure returns (uint256) {
        return 1;
    }

    function decodeAddress(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        return uint160(address(abi.decode(encoded, (address))));
    }

    function decodeFixedBytes(bytes memory encoded)
        external
        pure
        returns (bytes4)
    {
        return abi.decode(encoded, (bytes4));
    }

    function decodeBool(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        bool decoded = abi.decode(encoded, (bool));
        return decoded ? 1 : 0;
    }

    function uint8Value(uint8 input) external pure returns (uint256) {
        return input;
    }

    function uint8Unused(uint8) external pure returns (uint256) {
        return 1;
    }

    function int8Unused(int8) external pure returns (uint256) {
        return 1;
    }

    function enumValue(AbiMalformedChoice input)
        external
        pure
        returns (uint256)
    {
        return uint256(input);
    }

    function enumUnused(AbiMalformedChoice)
        external
        pure
        returns (uint256)
    {
        return 1;
    }

    function int8Value(int8 input) external pure returns (int256) {
        return input;
    }

    function decodeUint8(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        return abi.decode(encoded, (uint8));
    }

    function decodeEnum(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        AbiMalformedChoice decoded =
            abi.decode(encoded, (AbiMalformedChoice));
        return uint256(decoded);
    }

    function decodeInt8(bytes memory encoded)
        external
        pure
        returns (int256)
    {
        return abi.decode(encoded, (int8));
    }

    function uint8ArrayFirst(uint8[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input[0];
    }

    function uint8ArrayLength(uint8[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input.length;
    }

    function uint8FixedArrayFirst(uint8[2] calldata input)
        external
        pure
        returns (uint256)
    {
        return input[0];
    }

    function uint8FixedArraySecond(uint8[2] calldata input)
        external
        pure
        returns (uint256)
    {
        return input[1];
    }

    function narrowPairFirst(NarrowPair calldata input)
        external
        pure
        returns (uint256)
    {
        return input.clean;
    }

    function narrowPairSecond(NarrowPair calldata input)
        external
        pure
        returns (uint256)
    {
        return input.dirty;
    }

    // Nested-dynamic CALLDATA aggregates: solc validates only the immediate
    // structure at decode and returns a calldata pointer; a structurally
    // malformed inner dynamic element/member is validated LAZILY on access.
    // Reading only `.length` / a sibling field must therefore succeed even
    // when an unread inner element is malformed, while ACCESSING the malformed
    // element must revert empty.
    function bytesArrayLength(bytes[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input.length;
    }

    function bytesArraySecondLength(bytes[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input[1].length;
    }

    function dynBytesPairFirst(DynBytesPair calldata input)
        external
        pure
        returns (uint256)
    {
        return input.clean;
    }

    function dynBytesPairSecondLength(DynBytesPair calldata input)
        external
        pure
        returns (uint256)
    {
        return input.dirty.length;
    }

    function decodeUint8Array(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        uint8[] memory decoded = abi.decode(encoded, (uint8[]));
        return decoded[0];
    }

    function decodeUint8FixedArray(bytes memory encoded)
        external
        pure
        returns (uint256)
    {
        uint8[2] memory decoded = abi.decode(encoded, (uint8[2]));
        return decoded[0];
    }

    function highLevelNarrowReturn(address target)
        external
        returns (uint256)
    {
        return AbiMalformedNarrowReturn(target).narrowValue();
    }

    function highLevelBoolReturn(address target)
        external
        returns (uint256)
    {
        return AbiMalformedBoolReturn(target).boolValue() ? 1 : 0;
    }

    function highLevelAddressReturn(address target)
        external
        returns (uint256)
    {
        return uint160(AbiMalformedAddressReturn(target).addressValue());
    }

    function highLevelFixedBytesReturn(address target)
        external
        returns (bytes4)
    {
        return AbiMalformedFixedBytesReturn(target).fixedBytesValue();
    }

    function highLevelIgnoredAddressReturn(address target)
        external
        returns (uint256)
    {
        (uint256 value,) =
            AbiMalformedIgnoredAddressReturn(target).pairValue();
        return value;
    }

    function highLevelIgnoredFixedBytesReturn(address target)
        external
        returns (uint256)
    {
        (uint256 value,) =
            AbiMalformedIgnoredFixedBytesReturn(target).pairValue();
        return value;
    }

    function externalFunctionIgnoredAddressReturn(address target)
        external
        returns (uint256)
    {
        function() external returns (uint256, address) pair =
            AbiMalformedIgnoredAddressReturn(target).pairValue;
        (uint256 value,) = pair();
        return value;
    }

    function externalFunctionIgnoredFixedBytesReturn(address target)
        external
        returns (uint256)
    {
        function() external returns (uint256, bytes4) pair =
            AbiMalformedIgnoredFixedBytesReturn(target).pairValue;
        (uint256 value,) = pair();
        return value;
    }

    function highLevelEnumReturn(address target)
        external
        returns (uint256)
    {
        return uint256(AbiMalformedEnumReturn(target).enumValue());
    }

    function highLevelBoolLocalTernary(address target)
        external
        returns (uint256)
    {
        uint256 value =
            AbiMalformedBoolReturn(target).boolValue() ? 1 : 0;
        return value;
    }

    function highLevelBoolAssignTernary(address target)
        external
        returns (uint256)
    {
        uint256 value;
        value = AbiMalformedBoolReturn(target).boolValue() ? 1 : 0;
        return value;
    }

    function highLevelBytesReturnLength(address target)
        external
        returns (uint256)
    {
        bytes memory value = AbiMalformedBytesReturn(target).bytesValue();
        return value.length;
    }

    function highLevelUint8ArrayReturnFirst(address target)
        external
        returns (uint256)
    {
        uint8[] memory value =
            AbiMalformedUint8ArrayReturn(target).uint8ArrayValue();
        return value[0];
    }

    function highLevelUint8FixedArrayReturnFirst(address target)
        external
        returns (uint256)
    {
        uint8[2] memory value =
            AbiMalformedUint8FixedArrayReturn(target)
                .uint8FixedArrayValue();
        return value[0];
    }
}
