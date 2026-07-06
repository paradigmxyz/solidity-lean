// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract AbstractFunctionAncestor {
    function inheritedValue(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract FunctionImplementation is AbstractFunctionAncestor {
    function inheritedValue(uint256 input)
        public
        pure
        virtual
        override
        returns (uint256)
    {
        return input + 2;
    }
}

contract FunctionDominance is
    AbstractFunctionAncestor,
    FunctionImplementation
{
    function run(uint256 input) external pure returns (uint256) {
        return inheritedValue(input);
    }
}

abstract contract AbstractModifierAncestor {
    modifier guarded() virtual;
}

contract ModifierImplementation is AbstractModifierAncestor {
    modifier guarded() virtual override {
        _;
    }
}

contract ModifierDominance is
    AbstractModifierAncestor,
    ModifierImplementation
{
    function run(uint256 input) external guarded returns (uint256) {
        return input + 4;
    }
}

interface MemoryIdentity {
    function identity(uint256[] memory values)
        external
        pure
        returns (uint256[] memory);
}

interface CalldataIdentity {
    function identity(uint256[] calldata values)
        external
        pure
        returns (uint256[] calldata);
}

contract ExternalLocationIdentity is MemoryIdentity, CalldataIdentity {
    function identity(uint256[] memory values)
        public
        pure
        override(MemoryIdentity, CalldataIdentity)
        returns (uint256[] memory)
    {
        return values;
    }
}

abstract contract IndependentAbstract {
    function resolvedValue(uint256 input)
        public
        pure
        virtual
        returns (uint256);
}

contract IndependentConcrete {
    function resolvedValue(uint256 input)
        public
        pure
        virtual
        returns (uint256)
    {
        return input + 3;
    }
}

contract ResolvedIndependentConflict is
    IndependentAbstract,
    IndependentConcrete
{
    function resolvedValue(uint256 input)
        public
        pure
        override(IndependentAbstract, IndependentConcrete)
        returns (uint256)
    {
        return input + 3;
    }
}

contract CallableIdentity {
    function pick(uint256 input) internal pure returns (uint256) {
        return input + 5;
    }

    function pick(address input) internal pure returns (uint256) {
        return uint160(input) + 6;
    }

    function runUint(uint256 input) external pure returns (uint256) {
        return pick(input);
    }

    function runAddress(address input) external pure returns (uint256) {
        return pick(input);
    }
}
