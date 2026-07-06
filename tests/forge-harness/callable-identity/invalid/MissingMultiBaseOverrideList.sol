// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract MissingListFirstBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

abstract contract MissingListSecondBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract MissingMultiBaseOverrideList is
    MissingListFirstBase,
    MissingListSecondBase
{
    function value(uint256 input)
        public
        pure
        override
        returns (uint256)
    {
        return input;
    }
}
