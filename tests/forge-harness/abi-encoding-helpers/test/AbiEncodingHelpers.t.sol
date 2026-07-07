// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {
    AbiEncodingHelpers,
    IAbiEncodingHelperTarget
} from "../src/AbiEncodingHelpers.sol";

contract AbiEncodingHelpersForgeTest {
    AbiEncodingHelpers private target = new AbiEncodingHelpers();

    function requireBytesEq(
        bytes memory actual,
        bytes memory expected,
        string memory label
    ) internal pure {
        require(keccak256(actual) == keccak256(expected), label);
    }

    function testPackedScalarsAndArrays() public {
        bytes memory payload = hex"010203";
        requireBytesEq(
            target.packedScalars(bytes1(0x42), 3, payload),
            abi.encodePacked(bytes1(0x42), uint256(3), payload),
            "packed scalars"
        );

        uint8[] memory values = new uint8[](2);
        values[0] = 1;
        values[1] = 2;
        requireBytesEq(
            target.packedUint8Array(values),
            abi.encodePacked(values),
            "packed array"
        );
    }

    function testPackedNarrowWidths() public view {
        requireBytesEq(target.packedU8(), hex"1234", "packed u8");
        requireBytesEq(
            target.packedMixedWidth(),
            hex"123456789a",
            "packed mixed width"
        );
        requireBytesEq(target.packedNegInt8(), hex"ff", "packed neg int8");
        requireBytesEq(target.packedUint32(), hex"789abcde", "packed u32");
        requireBytesEq(target.packedBoolMix(), hex"010007", "packed bool mix");
        requireBytesEq(target.packedEnum(), hex"02", "packed enum");
    }

    function testPackedExternalFunction() public {
        function(uint256) external returns (uint256) fn =
            IAbiEncodingHelperTarget(address(uint160(0x1234))).ping;

        requireBytesEq(
            target.packedExternalFunction(fn),
            abi.encodePacked(fn),
            "packed function"
        );
    }

    function testSelectorAndSignatureEncoding() public {
        bytes4 selector =
            bytes4(keccak256("transfer(address,uint256)"));
        address who = address(uint160(0x1234));

        requireBytesEq(
            target.selectorCall(selector, who, 9),
            abi.encodeWithSelector(selector, who, 9),
            "selector"
        );
        requireBytesEq(
            target.signatureCall(who, 9),
            abi.encodeWithSignature("transfer(address,uint256)", who, 9),
            "signature"
        );
        requireBytesEq(
            target.runtimeSignatureCall("transfer(address,uint256)", who, 9),
            abi.encodeWithSignature("transfer(address,uint256)", who, 9),
            "runtime signature"
        );
    }

    function testConcatBuiltins() public {
        requireBytesEq(
            target.concatBytes(hex"0102", hex"0304"),
            bytes.concat(bytes1(0x41), hex"0102", hex"0304", hex"42"),
            "bytes concat"
        );
        requireBytesEq(
            bytes(target.concatString("x", "y")),
            bytes(string.concat("a", unicode"é", "x", "y")),
            "string concat"
        );
    }
}
