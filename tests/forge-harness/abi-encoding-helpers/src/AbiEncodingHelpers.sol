// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface IAbiEncodingHelperTarget {
    function ping(uint256 value) external returns (uint256);
}

contract AbiEncodingHelpers {
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
