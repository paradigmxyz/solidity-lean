// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract UnassignedStorageReturn {
    function bad() internal returns (uint256[] storage result) {}
}
