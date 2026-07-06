// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataReturn {
    function bad(uint256[] memory input)
        public
        pure
        returns (uint256[] calldata)
    {
        return input;
    }
}
