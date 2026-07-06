// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExplicitUnassignedReturn {
    function bad() internal pure returns (uint256[] calldata result) {
        return result;
    }
}
