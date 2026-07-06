// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ImplementedFunctionBase {
    function value(uint256 input) public pure virtual returns (uint256) {
        return input + 1;
    }
}

abstract contract BodylessFunctionOverride is ImplementedFunctionBase {
    function value(uint256 input)
        public
        pure
        virtual
        override
        returns (uint256);
}
