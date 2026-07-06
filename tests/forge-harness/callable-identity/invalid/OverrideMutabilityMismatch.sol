// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract MutabilityBase {
    function value(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract OverrideMutabilityMismatch is MutabilityBase {
    function value(uint256 input)
        public
        view
        override
        returns (uint256)
    {
        return input;
    }
}
