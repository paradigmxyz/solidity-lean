// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract ReturnTypeBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract OverrideReturnTypeMismatch is ReturnTypeBase {
    function value(uint256 input)
        public
        pure
        override
        returns (bool)
    {
        return input == 0;
    }
}
