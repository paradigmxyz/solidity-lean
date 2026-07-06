// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library CalldataOriginLibrary {
    function publicLength(uint256[] calldata values)
        public
        pure
        returns (uint256)
    {
        return values.length;
    }

    function libraryInternalLength(uint256[] calldata values)
        internal
        pure
        returns (uint256)
    {
        return values.length;
    }
}

contract CalldataOrigins {
    using CalldataOriginLibrary for uint256[];

    function localAlias(uint256[] calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] calldata local = input;
        return (local.length, local[0]);
    }

    function returnAlias(uint256[] calldata input)
        external
        pure
        returns (uint256[] calldata)
    {
        return input;
    }

    function internalLength(uint256[] calldata input)
        internal
        pure
        returns (uint256)
    {
        return input.length;
    }

    function internalAlias(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        return internalLength(input);
    }

    function calldataToMemory(uint256[] calldata input)
        external
        pure
        returns (uint256, uint256)
    {
        uint256[] memory copied = input;
        copied[0] = 9;
        return (input[0], copied[0]);
    }

    function reassignAlias(
        uint256[] calldata first,
        uint256[] calldata second
    ) external pure returns (uint256, uint256) {
        uint256[] calldata local = first;
        uint256 before = local[0];
        local = second;
        return (before, local[0]);
    }

    function pair(
        uint256[] calldata left,
        uint256[] calldata right
    ) internal pure returns (uint256[] calldata, uint256[] calldata) {
        return (left, right);
    }

    function tupleAlias(
        uint256[] calldata left,
        uint256[] calldata right
    ) external pure returns (uint256, uint256) {
        (uint256[] calldata leftAlias, uint256[] calldata rightAlias) =
            pair(left, right);
        return (leftAlias[0], rightAlias[0]);
    }

    function externalLength(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        return input.length;
    }

    function memoryToExternal(uint256[] memory input)
        public
        view
        returns (uint256)
    {
        return this.externalLength(input);
    }

    function memoryToPublicLibrary(uint256[] memory input)
        public
        view
        returns (uint256)
    {
        uint256 result = CalldataOriginLibrary.publicLength(input);
        return result;
    }

    function memoryToUsingPublicLibrary(uint256[] memory input)
        public
        view
        returns (uint256)
    {
        uint256 result = input.publicLength();
        return result;
    }

    function calldataToInternalLibrary(uint256[] calldata input)
        external
        pure
        returns (uint256)
    {
        return CalldataOriginLibrary.libraryInternalLength(input);
    }
}
