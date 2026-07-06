// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract T {}

contract ContractCode {
    function bad(T target) external view returns (bytes memory) {
        return target.code;
    }
}
