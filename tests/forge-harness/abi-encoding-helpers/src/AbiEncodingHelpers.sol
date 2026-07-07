// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface IAbiEncodingHelperTarget {
    function ping(uint256 value) external returns (uint256);
}

contract AbiEncodingHelpers {
    enum Direction { Left, Right, Up }

    // Narrow top-level scalars must pack to their true width (N/8 bytes), not
    // the 32-byte ABI padding. Regression lane for the B/C W1 soundness fix.
    function packedU8() external pure returns (bytes memory) {
        uint8 a = 0x12;
        uint8 b = 0x34;
        return abi.encodePacked(a, b);
    }

    function packedMixedWidth() external pure returns (bytes memory) {
        uint16 a = 0x1234;
        uint24 b = 0x56789a;
        return abi.encodePacked(a, b);
    }

    function packedNegInt8() external pure returns (bytes memory) {
        int8 a = -1;
        return abi.encodePacked(a);
    }

    function packedUint32() external pure returns (bytes memory) {
        uint32 a = 0x789abcde;
        return abi.encodePacked(a);
    }

    function packedBoolMix() external pure returns (bytes memory) {
        uint8 c = 7;
        return abi.encodePacked(true, false, c);
    }

    function packedEnum() external pure returns (bytes memory) {
        return abi.encodePacked(Direction.Up);
    }

    function packedScalars(
        bytes1 tag,
        uint256 value,
        bytes calldata payload
    ) external pure returns (bytes memory) {
        return abi.encodePacked(tag, value, payload);
    }

    function packedUint8Array(uint8[] memory values)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(values);
    }

    function packedExternalFunction(
        function(uint256) external returns (uint256) fn
    ) external pure returns (bytes memory) {
        return abi.encodePacked(fn);
    }

    function selectorCall(bytes4 selector, address who, uint256 amount)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSelector(selector, who, amount);
    }

    function signatureCall(address who, uint256 amount)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodeWithSignature(
            "transfer(address,uint256)",
            who,
            amount
        );
    }

    function runtimeSignatureCall(
        string calldata signature,
        address who,
        uint256 amount
    ) external pure returns (bytes memory) {
        return abi.encodeWithSignature(signature, who, amount);
    }

    function concatBytes(bytes calldata prefix, bytes calldata suffix)
        external
        pure
        returns (bytes memory)
    {
        return bytes.concat(bytes1(0x41), prefix, suffix, hex"42");
    }

    function concatString(string calldata prefix, string calldata suffix)
        external
        pure
        returns (string memory)
    {
        return string.concat("a", unicode"é", prefix, suffix);
    }
}
