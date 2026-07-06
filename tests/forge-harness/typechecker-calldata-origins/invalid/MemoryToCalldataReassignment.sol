// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataReassignment {
    function bad(
        uint256[] memory memoryInput,
        uint256[] calldata calldataInput
    ) public pure returns (uint256) {
        uint256[] calldata local = calldataInput;
        local = memoryInput;
        return local.length;
    }
}
