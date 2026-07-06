// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/AbiMalformed.sol";

interface AbiMalformedVm {
    function deployCode(string calldata artifact, bytes calldata args)
        external
        returns (address deployed);
}

contract AbiMalformedForgeTest {
    AbiMalformedVm private constant VM = AbiMalformedVm(
        address(uint160(uint256(keccak256("hevm cheat code"))))
    );

    AbiMalformed private target;

    function setUp() public {
        target = new AbiMalformed(1);
    }

    function callBytesLength(bytes memory args)
        internal
        returns (bool success, bytes memory output)
    {
        return address(target).call(
            bytes.concat(AbiMalformed.bytesLength.selector, args)
        );
    }

    function callDecodeBytes(bytes memory encoded)
        internal
        returns (bool success, bytes memory output)
    {
        return address(target).call(
            abi.encodeCall(AbiMalformed.decodeBytes, (encoded))
        );
    }

    function validOneByte() internal pure returns (bytes memory) {
        return abi.encode(bytes("a"));
    }

    function missingPadding() internal pure returns (bytes memory) {
        return bytes.concat(bytes32(uint256(32)), bytes32(uint256(1)), "a");
    }

    function nonzeroPadding() internal pure returns (bytes memory) {
        return bytes.concat(
            bytes32(uint256(32)),
            bytes32(uint256(1)),
            "a",
            bytes31(uint248(1))
        );
    }

    function unalignedOffset() internal pure returns (bytes memory) {
        return bytes.concat(
            bytes32(uint256(33)),
            hex"00",
            bytes32(uint256(1)),
            "a",
            bytes31(0)
        );
    }

    function requireWord(bytes memory output, uint256 expected)
        internal
        pure
    {
        require(output.length == 32, "output length");
        require(abi.decode(output, (uint256)) == expected, "output word");
    }

    function requireHighLevelMalformedBool(
        bytes memory payload,
        string memory reason
    ) internal {
        (bool success, bytes memory output) = address(target).call(payload);
        require(!success, reason);
        require(output.length == 0, "bool return data");
    }

    function testExternalArgumentDecoderBoundsAndPermissiveness() public {
        (bool valid, bytes memory validOutput) = callBytesLength(validOneByte());
        require(valid, "valid");
        requireWord(validOutput, 1);

        (bool missing, bytes memory missingOutput) =
            callBytesLength(missingPadding());
        require(missing, "missing padding");
        requireWord(missingOutput, 1);

        (bool nonzero, bytes memory nonzeroOutput) =
            callBytesLength(nonzeroPadding());
        require(nonzero, "nonzero padding");
        requireWord(nonzeroOutput, 1);

        (bool trailing, bytes memory trailingOutput) =
            callBytesLength(bytes.concat(validOneByte(), hex"ff"));
        require(trailing, "trailing junk");
        requireWord(trailingOutput, 1);

        (bool unaligned, bytes memory unalignedOutput) =
            callBytesLength(unalignedOffset());
        require(unaligned, "unaligned offset");
        requireWord(unalignedOutput, 1);

        (bool aliasesHead, bytes memory aliasesHeadOutput) =
            callBytesLength(bytes.concat(bytes32(0)));
        require(aliasesHead, "head alias");
        requireWord(aliasesHeadOutput, 0);
    }

    function testAbiDecodeBoundsAndPermissiveness() public {
        (bool valid, bytes memory validOutput) = callDecodeBytes(validOneByte());
        require(valid, "valid");
        requireWord(validOutput, 1);

        (bool missing, bytes memory missingOutput) =
            callDecodeBytes(missingPadding());
        require(missing, "missing padding");
        requireWord(missingOutput, 1);

        (bool nonzero, bytes memory nonzeroOutput) =
            callDecodeBytes(nonzeroPadding());
        require(nonzero, "nonzero padding");
        requireWord(nonzeroOutput, 1);

        (bool trailing, bytes memory trailingOutput) =
            callDecodeBytes(bytes.concat(validOneByte(), hex"ff"));
        require(trailing, "trailing junk");
        requireWord(trailingOutput, 1);

        (bool unaligned, bytes memory unalignedOutput) =
            callDecodeBytes(unalignedOffset());
        require(unaligned, "unaligned offset");
        requireWord(unalignedOutput, 1);

        (bool aliasesHead, bytes memory aliasesHeadOutput) =
            callDecodeBytes(bytes.concat(bytes32(0)));
        require(aliasesHead, "head alias");
        requireWord(aliasesHeadOutput, 0);
    }

    function testExternalStaticCanonicalDecoding() public {
        bytes memory malformedBool = bytes.concat(
            AbiMalformed.boolValue.selector,
            bytes32(uint256(2))
        );
        (bool boolSuccess, bytes memory boolOutput) =
            address(target).call(malformedBool);
        require(!boolSuccess, "bool value");
        require(boolOutput.length == 0, "bool revert data");

        bytes memory malformedAddress = bytes.concat(
            AbiMalformed.addressValue.selector,
            bytes32(uint256(1) << 160)
        );
        (bool addressSuccess, bytes memory addressOutput) =
            address(target).call(malformedAddress);
        require(!addressSuccess, "address high bits");
        require(addressOutput.length == 0, "address revert data");

        bytes memory malformedFixed = bytes.concat(
            AbiMalformed.fixedBytesValue.selector,
            hex"01020304",
            bytes28(uint224(1))
        );
        (bool fixedSuccess, bytes memory fixedOutput) =
            address(target).call(malformedFixed);
        require(!fixedSuccess, "fixed bytes padding");
        require(fixedOutput.length == 0, "fixed revert data");

        bytes memory malformedEnum = bytes.concat(
            AbiMalformed.enumValue.selector,
            bytes32(uint256(2))
        );
        (bool enumSuccess, bytes memory enumOutput) =
            address(target).call(malformedEnum);
        require(!enumSuccess, "enum value");
        require(enumOutput.length == 0, "enum revert data");
    }

    function testAbiDecodeStaticCanonicalDecoding() public {
        (bool boolSuccess, bytes memory boolOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeBool,
                (bytes.concat(bytes32(uint256(2))))
            )
        );
        require(!boolSuccess, "bool value");
        require(boolOutput.length == 0, "bool revert data");

        (bool addressSuccess, bytes memory addressOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeAddress,
                (bytes.concat(bytes32(uint256(1) << 160)))
            )
        );
        require(!addressSuccess, "address high bits");
        require(addressOutput.length == 0, "address revert data");

        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeFixedBytes,
                (bytes.concat(hex"01020304", bytes28(uint224(1))))
            )
        );
        require(!fixedSuccess, "fixed bytes padding");
        require(fixedOutput.length == 0, "fixed revert data");

        (bool enumSuccess, bytes memory enumOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeEnum,
                (bytes.concat(bytes32(uint256(2))))
            )
        );
        require(!enumSuccess, "enum value");
        require(enumOutput.length == 0, "enum revert data");
    }

    function testExternalNarrowIntegerCanonicalDecoding() public {
        (bool uintSuccess, bytes memory uintOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8Value.selector,
                bytes32(uint256(256))
            )
        );
        require(!uintSuccess, "uint8 range");
        require(uintOutput.length == 0, "uint8 revert data");

        (bool intSuccess, bytes memory intOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.int8Value.selector,
                bytes32(uint256(255))
            )
        );
        require(!intSuccess, "int8 sign extension");
        require(intOutput.length == 0, "int8 revert data");
    }

    function testExternalUnusedScalarCanonicalDecoding() public {
        (bool boolSuccess, bytes memory boolOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.boolUnused.selector,
                bytes32(uint256(2))
            )
        );
        require(!boolSuccess, "unused bool value");
        require(boolOutput.length == 0, "unused bool revert data");

        (bool addressSuccess, bytes memory addressOutput) =
            address(target).call(
                bytes.concat(
                    AbiMalformed.addressUnused.selector,
                    bytes32(uint256(1) << 160)
                )
            );
        require(!addressSuccess, "unused address value");
        require(addressOutput.length == 0, "unused address revert data");

        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.fixedBytesUnused.selector,
                hex"01020304",
                bytes28(uint224(1))
            )
        );
        require(!fixedSuccess, "unused fixed bytes value");
        require(fixedOutput.length == 0, "unused fixed bytes revert data");

        (bool enumSuccess, bytes memory enumOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.enumUnused.selector,
                bytes32(uint256(2))
            )
        );
        require(!enumSuccess, "unused enum value");
        require(enumOutput.length == 0, "unused enum revert data");

        (bool uintSuccess, bytes memory uintOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8Unused.selector,
                bytes32(uint256(256))
            )
        );
        require(!uintSuccess, "unused uint8 range");
        require(uintOutput.length == 0, "unused uint8 revert data");

        (bool intSuccess, bytes memory intOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.int8Unused.selector,
                bytes32(uint256(255))
            )
        );
        require(!intSuccess, "unused int8 sign extension");
        require(intOutput.length == 0, "unused int8 revert data");
    }

    function testAbiDecodeNarrowIntegerCanonicalDecoding() public {
        (bool uintSuccess, bytes memory uintOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeUint8,
                (bytes.concat(bytes32(uint256(256))))
            )
        );
        require(!uintSuccess, "uint8 range");
        require(uintOutput.length == 0, "uint8 revert data");

        (bool intSuccess, bytes memory intOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeInt8,
                (bytes.concat(bytes32(uint256(255))))
            )
        );
        require(!intSuccess, "int8 sign extension");
        require(intOutput.length == 0, "int8 revert data");
    }

    function malformedUint8Array() internal pure returns (bytes memory) {
        return bytes.concat(
            bytes32(uint256(32)),
            bytes32(uint256(1)),
            bytes32(uint256(256))
        );
    }

    function malformedUint8FixedArrayFirstElement()
        internal
        pure
        returns (bytes memory)
    {
        return bytes.concat(bytes32(uint256(256)), bytes32(uint256(7)));
    }

    function malformedUint8FixedArraySecondElement()
        internal
        pure
        returns (bytes memory)
    {
        return bytes.concat(bytes32(uint256(7)), bytes32(uint256(256)));
    }

    function malformedNarrowPairSecondField()
        internal
        pure
        returns (bytes memory)
    {
        return bytes.concat(bytes32(uint256(7)), bytes32(uint256(256)));
    }

    function testExternalNestedNarrowIntegerCanonicalDecoding() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8ArrayFirst.selector,
                malformedUint8Array()
            )
        );
        require(!success, "uint8 array element");
        require(output.length == 0, "uint8 array revert data");

        (bool lengthSuccess, bytes memory lengthOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8ArrayLength.selector,
                malformedUint8Array()
            )
        );
        require(lengthSuccess, "uint8 array lazy length");
        requireWord(lengthOutput, 1);

        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8FixedArrayFirst.selector,
                malformedUint8FixedArrayFirstElement()
            )
        );
        require(!fixedSuccess, "uint8 fixed array element");
        require(fixedOutput.length == 0, "uint8 fixed array revert data");

        (bool lazySuccess, bytes memory lazyOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8FixedArrayFirst.selector,
                malformedUint8FixedArraySecondElement()
            )
        );
        require(lazySuccess, "uint8 fixed array lazy first");
        requireWord(lazyOutput, 7);

        (bool secondSuccess, bytes memory secondOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.uint8FixedArraySecond.selector,
                malformedUint8FixedArraySecondElement()
            )
        );
        require(!secondSuccess, "uint8 fixed array second element");
        require(secondOutput.length == 0, "uint8 fixed array second data");

        (bool pairSuccess, bytes memory pairOutput) = address(target).call(
            bytes.concat(
                AbiMalformed.narrowPairFirst.selector,
                malformedNarrowPairSecondField()
            )
        );
        require(pairSuccess, "narrow pair lazy first");
        requireWord(pairOutput, 7);

        (bool pairSecondSuccess, bytes memory pairSecondOutput) =
            address(target).call(
                bytes.concat(
                    AbiMalformed.narrowPairSecond.selector,
                    malformedNarrowPairSecondField()
                )
            );
        require(!pairSecondSuccess, "narrow pair second field");
        require(pairSecondOutput.length == 0, "narrow pair second data");
    }

    function testAbiDecodeNestedNarrowIntegerCanonicalDecoding() public {
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeUint8Array,
                (malformedUint8Array())
            )
        );
        require(!success, "uint8 array element");
        require(output.length == 0, "uint8 array revert data");

        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.decodeUint8FixedArray,
                (malformedUint8FixedArraySecondElement())
            )
        );
        require(!fixedSuccess, "uint8 fixed array element");
        require(fixedOutput.length == 0, "uint8 fixed array revert data");
    }

    function testGeneratedGetterCanonicalDecoding() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                bytes4(keccak256("narrowMap(uint8)")),
                bytes32(uint256(256))
            )
        );
        require(!success, "getter uint8 key");
        require(output.length == 0, "getter revert data");
    }

    function testConstructorCanonicalDecoding() public {
        (bool success, bytes memory output) = address(VM).call(
            abi.encodeCall(
                AbiMalformedVm.deployCode,
                (
                    "src/AbiMalformed.sol:AbiMalformed",
                    bytes.concat(bytes32(uint256(256)))
                )
            )
        );
        require(!success, "constructor uint8");
        require(output.length == 0, "constructor revert data");
    }

    function testConstructorNestedNarrowIntegerCanonicalDecoding() public {
        (bool arraySuccess, bytes memory arrayOutput) = address(VM).call(
            abi.encodeCall(
                AbiMalformedVm.deployCode,
                (
                    "src/AbiMalformed.sol:AbiMalformedConstructorArrayLength",
                    malformedUint8Array()
                )
            )
        );
        require(!arraySuccess, "constructor uint8 array");
        require(arrayOutput.length == 0, "constructor array revert data");

        (bool fixedSuccess, bytes memory fixedOutput) = address(VM).call(
            abi.encodeCall(
                AbiMalformedVm.deployCode,
                (
                    "src/AbiMalformed.sol:AbiMalformedConstructorFixedArrayFirst",
                    malformedUint8FixedArraySecondElement()
                )
            )
        );
        require(!fixedSuccess, "constructor uint8 fixed array");
        require(fixedOutput.length == 0, "constructor fixed revert data");

        (bool pairSuccess, bytes memory pairOutput) = address(VM).call(
            abi.encodeCall(
                AbiMalformedVm.deployCode,
                (
                    "src/AbiMalformed.sol:AbiMalformedConstructorPairFirst",
                    malformedNarrowPairSecondField()
                )
            )
        );
        require(!pairSuccess, "constructor narrow pair");
        require(pairOutput.length == 0, "constructor pair revert data");
    }

    function testHighLevelMalformedNarrowReturn() public {
        AbiMalformedReturnTarget malformed = new AbiMalformedReturnTarget();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelNarrowReturn,
                (address(malformed))
            )
        );
        require(!success, "narrow return");
        require(output.length == 0, "narrow return data");
    }

    function testHighLevelMalformedEnumReturn() public {
        AbiMalformedEnumReturnTarget malformed =
            new AbiMalformedEnumReturnTarget();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelEnumReturn,
                (address(malformed))
            )
        );
        require(!success, "enum return");
        require(output.length == 0, "enum return data");
    }

    function testHighLevelMalformedBoolReturn() public {
        AbiMalformedBoolReturnTarget malformed =
            new AbiMalformedBoolReturnTarget();
        address malformedAddress = address(malformed);
        requireHighLevelMalformedBool(
            abi.encodeCall(
                AbiMalformed.highLevelBoolReturn,
                (malformedAddress)
            ),
            "bool return"
        );
        requireHighLevelMalformedBool(
            abi.encodeCall(
                AbiMalformed.highLevelBoolLocalTernary,
                (malformedAddress)
            ),
            "bool local ternary"
        );
        requireHighLevelMalformedBool(
            abi.encodeCall(
                AbiMalformed.highLevelBoolAssignTernary,
                (malformedAddress)
            ),
            "bool assign ternary"
        );
    }

    function testHighLevelMalformedAddressAndFixedBytesReturn() public {
        AbiMalformedAddressReturnTarget malformedAddress =
            new AbiMalformedAddressReturnTarget();
        (bool addressSuccess, bytes memory addressOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelAddressReturn,
                (address(malformedAddress))
            )
        );
        require(!addressSuccess, "address return");
        require(addressOutput.length == 0, "address return data");

        AbiMalformedFixedBytesReturnTarget malformedFixed =
            new AbiMalformedFixedBytesReturnTarget();
        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelFixedBytesReturn,
                (address(malformedFixed))
            )
        );
        require(!fixedSuccess, "fixed bytes return");
        require(fixedOutput.length == 0, "fixed return data");
    }

    function testHighLevelIgnoredMalformedReturnComponents() public {
        AbiMalformedIgnoredAddressReturnTarget malformedAddress =
            new AbiMalformedIgnoredAddressReturnTarget();
        (bool addressSuccess, bytes memory addressOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelIgnoredAddressReturn,
                (address(malformedAddress))
            )
        );
        require(!addressSuccess, "ignored address return");
        require(addressOutput.length == 0, "ignored address data");

        AbiMalformedIgnoredFixedBytesReturnTarget malformedFixed =
            new AbiMalformedIgnoredFixedBytesReturnTarget();
        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelIgnoredFixedBytesReturn,
                (address(malformedFixed))
            )
        );
        require(!fixedSuccess, "ignored fixed return");
        require(fixedOutput.length == 0, "ignored fixed data");
    }

    function testExternalFunctionIgnoredMalformedReturnComponents() public {
        AbiMalformedIgnoredAddressReturnTarget malformedAddress =
            new AbiMalformedIgnoredAddressReturnTarget();
        (bool addressSuccess, bytes memory addressOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.externalFunctionIgnoredAddressReturn,
                (address(malformedAddress))
            )
        );
        require(!addressSuccess, "function ignored address return");
        require(addressOutput.length == 0, "function ignored address data");

        AbiMalformedIgnoredFixedBytesReturnTarget malformedFixed =
            new AbiMalformedIgnoredFixedBytesReturnTarget();
        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.externalFunctionIgnoredFixedBytesReturn,
                (address(malformedFixed))
            )
        );
        require(!fixedSuccess, "function ignored fixed return");
        require(fixedOutput.length == 0, "function ignored fixed data");
    }

    function testHighLevelDynamicReturnBoundsAndPermissiveness() public {
        AbiMalformedBytesReturnTarget malformed =
            new AbiMalformedBytesReturnTarget();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelBytesReturnLength,
                (address(malformed))
            )
        );
        require(success, "bytes return");
        requireWord(output, 1);
    }

    function testHighLevelNestedNarrowReturnCanonicalDecoding() public {
        AbiMalformedArrayReturnTarget malformed =
            new AbiMalformedArrayReturnTarget();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelUint8ArrayReturnFirst,
                (address(malformed))
            )
        );
        require(!success, "uint8 array return");
        require(output.length == 0, "uint8 array return data");

        AbiMalformedFixedArrayReturnTarget fixedMalformed =
            new AbiMalformedFixedArrayReturnTarget();
        (bool fixedSuccess, bytes memory fixedOutput) = address(target).call(
            abi.encodeCall(
                AbiMalformed.highLevelUint8FixedArrayReturnFirst,
                (address(fixedMalformed))
            )
        );
        require(!fixedSuccess, "uint8 fixed array return");
        require(fixedOutput.length == 0, "uint8 fixed array return data");
    }
}
