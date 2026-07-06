// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract T {}

contract ContractBalance {
    function bad(T target) external view returns (uint256) {
        return target.balance;
    }
}
