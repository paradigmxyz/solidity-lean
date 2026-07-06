// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract InternalLocationBase {
    function identity(uint256[] memory values)
        internal
        pure
        virtual
        returns (uint256[] memory);
}

contract InternalLocation is InternalLocationBase {
    function identity(uint256[] calldata values)
        internal
        pure
        override
        returns (uint256[] calldata)
    {
        return values;
    }
}
