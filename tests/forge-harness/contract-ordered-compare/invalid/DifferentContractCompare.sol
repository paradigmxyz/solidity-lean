// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 rejects ordered comparison across DIFFERENT, unrelated contract
// types (TypeError: "Built-in binary operator < cannot be applied to types
// contract A and contract B" — the two operands have no common type). Same- or
// related-contract ordered comparison is accepted; this pins that the fix keeps
// unrelated contracts rejected (the common-type machinery drives this).
contract A {}
contract B {}

contract DifferentContractCompare {
    function bad(A a, B b) external pure returns (bool) {
        return a < b;
    }
}
