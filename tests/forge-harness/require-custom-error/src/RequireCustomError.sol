// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// FILE-LEVEL (free) custom error, declared outside any contract.
error FreeErr(uint256 x);

contract RequireCustomErrorHarnessTarget {
    // CONTRACT-LEVEL custom error.
    error MemberErr(uint256 x);

    // require(cond, MemberErr(a)): a contract-level declared error as the
    // second argument. On false, reverts with MemberErr's selector ++
    // abi.encode(a) (custom-error revert), NOT Error(string).
    function c(uint256 a) external pure returns (uint256) {
        require(a > 0, MemberErr(a));
        return a;
    }

    // require(cond, FreeErr(a)): a FILE-LEVEL (free) declared error as the
    // second argument. Must behave identically to the contract-level case:
    // on false, reverts with FreeErr's selector ++ abi.encode(a).
    function fr(uint256 a) external pure returns (uint256) {
        require(a > 0, FreeErr(a));
        return a;
    }
}
