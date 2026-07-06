// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract PublicReturnLocationBase {
    function identity(uint256[] calldata values)
        public
        pure
        virtual
        returns (uint256[] memory);
}

contract PublicReturnLocation is PublicReturnLocationBase {
    function identity(uint256[] calldata values)
        public
        pure
        override
        returns (uint256[] calldata)
    {
        return values;
    }
}
