// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract PublicParamLocationBase {
    function readLength(uint256[] memory values)
        public
        pure
        virtual
        returns (uint256);
}

contract PublicParamLocation is PublicParamLocationBase {
    function readLength(uint256[] calldata values)
        public
        pure
        override
        returns (uint256)
    {
        return values.length;
    }
}
