// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ContractOrderedCompareHarnessTarget} from "../src/ContractOrderedCompare.sol";

contract ContractOrderedCompareForgeTest {
    ContractOrderedCompareHarnessTarget internal target;
    ContractOrderedCompareHarnessTarget internal a;
    ContractOrderedCompareHarnessTarget internal b;

    function setUp() public {
        target = new ContractOrderedCompareHarnessTarget();
        a = new ContractOrderedCompareHarnessTarget();
        b = new ContractOrderedCompareHarnessTarget();
    }

    // Ordered contract comparison equals the unsigned comparison of the two
    // deployed addresses, for all four operators.
    function testMatchesAddressCompare() external {
        require(target.lt(a, b) == (address(a) < address(b)), "lt");
        require(target.gt(a, b) == (address(a) > address(b)), "gt");
        require(target.le(a, b) == (address(a) <= address(b)), "le");
        require(target.ge(a, b) == (address(a) >= address(b)), "ge");
    }

    // Deterministic order properties (independent of the actual addresses):
    // `<` is irreflexive, `<=` is reflexive, `this < this` is false and
    // `this <= this` is true, and strict order is antisymmetric for two distinct
    // deployed contracts.
    function testOrderProperties() external {
        require(!target.ltSelf(a), "ltSelf");
        require(target.leSelf(a), "leSelf");
        require(!target.ltThis(), "ltThis");
        require(target.leThis(), "leThis");
        require(address(a) != address(b), "distinct");
        require(target.lt(a, b) != target.lt(b, a), "antisym");
    }
}
