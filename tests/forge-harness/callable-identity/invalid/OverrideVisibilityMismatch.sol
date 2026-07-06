// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract VisibilityBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract OverrideVisibilityMismatch is VisibilityBase {
    function value(uint256 input)
        external
        pure
        override
        returns (uint256)
    {
        return input;
    }
}
