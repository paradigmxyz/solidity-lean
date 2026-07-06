// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract LocationOnlyOverload {
    function locate(uint256[] memory) internal pure {}
    function locate(uint256[] calldata) internal pure {}
}
