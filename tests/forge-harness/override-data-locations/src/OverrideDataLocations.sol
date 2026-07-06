// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

function freeMemory(uint256[] memory values)
    pure
    returns (uint256[] memory)
{
    return values;
}

function freeCalldata(uint256[] calldata values)
    pure
    returns (uint256[] calldata)
{
    return values;
}

function freeStorage(uint256[] storage values)
    pure
    returns (uint256[] storage)
{
    return values;
}

library OverrideLocationLibrary {
    function publicStorage(uint256[] storage values)
        public
        view
        returns (uint256)
    {
        return values.length;
    }

    function externalMemory(uint256[] memory values)
        external
        pure
        returns (uint256[] memory)
    {
        return values;
    }

    function externalCalldata(uint256[] calldata values)
        external
        pure
        returns (uint256[] calldata)
    {
        return values;
    }
}

abstract contract OverrideLocationBase {
    uint256[] internal stored;

    modifier memoryModifier(uint256[] memory values) {
        require(values.length > 0);
        _;
    }

    modifier calldataModifier(uint256[] calldata values) {
        require(values.length > 0);
        _;
    }

    modifier storageModifier(uint256[] storage values) {
        require(values.length > 0);
        _;
    }

    function publicMemory(uint256[] memory values)
        public
        pure
        virtual
        returns (uint256[] memory)
    {
        return values;
    }

    function publicCalldata(uint256[] calldata values)
        public
        pure
        virtual
        returns (uint256[] calldata)
    {
        return values;
    }

    function externalMemory(uint256[] memory values)
        external
        pure
        virtual
        returns (uint256[] memory)
    {
        return values;
    }

    function externalCalldata(uint256[] calldata values)
        external
        pure
        virtual
        returns (uint256[] calldata)
    {
        return values;
    }

    function internalStorage(uint256[] storage values)
        internal
        pure
        returns (uint256[] storage)
    {
        return values;
    }

    function privateCalldata(uint256[] calldata values)
        private
        pure
        returns (uint256[] calldata)
    {
        return values;
    }
}

contract OverrideDataLocations is OverrideLocationBase {
    constructor(uint256[] memory initial) {
        stored = initial;
    }

    function publicMemory(uint256[] memory values)
        public
        pure
        override
        returns (uint256[] memory)
    {
        return values;
    }

    function publicCalldata(uint256[] calldata values)
        public
        pure
        override
        returns (uint256[] calldata)
    {
        return values;
    }

    function externalMemory(uint256[] calldata values)
        external
        pure
        override
        returns (uint256[] calldata)
    {
        return values;
    }

    function externalCalldata(uint256[] memory values)
        external
        pure
        override
        returns (uint256[] memory)
    {
        return values;
    }

    function freeMemoryRoundTrip(uint256[] memory values)
        public
        pure
        returns (uint256[] memory)
    {
        uint256[] memory aliasValue = freeMemory(values);
        aliasValue[0] = 31;
        return values;
    }

    function freeCalldataRoundTrip(uint256[] calldata values)
        public
        pure
        returns (uint256[] calldata)
    {
        return freeCalldata(values);
    }

    function freeStorageRoundTrip()
        external
        returns (uint256, uint256, uint256)
    {
        delete stored;
        stored.push(5);
        uint256[] storage aliasValue = freeStorage(stored);
        aliasValue.push(6);
        aliasValue[0] = 9;
        return (stored.length, stored[0], stored[1]);
    }
}
