// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReferenceDelete {
    struct S {
        uint256 value;
    }

    function dynamicArray(uint256[] memory input)
        external
        pure
        returns (uint256 deletedLength, uint256 aliasLength)
    {
        uint256[] memory aliasValue = input;
        delete input;
        return (input.length, aliasValue.length);
    }

    function fixedArray(uint256[2] memory input)
        external
        pure
        returns (uint256 deletedValue, uint256 aliasValue)
    {
        uint256[2] memory aliasArray = input;
        delete input;
        return (input[0], aliasArray[0]);
    }

    function structValue(S memory input)
        external
        pure
        returns (uint256 deletedValue, uint256 aliasValue)
    {
        S memory aliasStruct = input;
        delete input;
        return (input.value, aliasStruct.value);
    }

    function bytesValue(bytes memory input)
        external
        pure
        returns (uint256 deletedLength, uint256 aliasLength)
    {
        bytes memory aliasValue = input;
        delete input;
        return (input.length, aliasValue.length);
    }

    function stringValue(string memory input)
        external
        pure
        returns (uint256 deletedLength, uint256 aliasLength)
    {
        string memory aliasValue = input;
        delete input;
        return (bytes(input).length, bytes(aliasValue).length);
    }

    function dynamicElement(uint256[] memory input)
        external
        pure
        returns (uint256 deletedValue, uint256 aliasValue)
    {
        uint256[] memory aliasArray = input;
        delete input[0];
        return (input[0], aliasArray[0]);
    }

    function structMember(S memory input)
        external
        pure
        returns (uint256 deletedValue, uint256 aliasValue)
    {
        S memory aliasStruct = input;
        delete input.value;
        return (input.value, aliasStruct.value);
    }
}
