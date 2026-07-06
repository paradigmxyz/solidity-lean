// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract ListMismatchFirstBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

abstract contract ListMismatchSecondBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract OverrideBaseListMismatch is
    ListMismatchFirstBase,
    ListMismatchSecondBase
{
    function value(uint256 input)
        public
        pure
        override(ListMismatchFirstBase)
        returns (uint256)
    {
        return input;
    }
}
