// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CalldataRefInternalHarnessTarget} from "../src/CalldataRefInternal.sol";

contract CalldataRefInternalForgeTest {
    CalldataRefInternalHarnessTarget private target =
        new CalldataRefInternalHarnessTarget();

    function xs3() internal pure returns (uint256[] memory xs) {
        xs = new uint256[](3);
        xs[0] = 3;
        xs[1] = 4;
        xs[2] = 5;
    }

    function testViaParams() public view {
        require(target.viaParams(xs3(), hex"0102") == 12001, "viaParams");
    }

    function testViaSlice() public view {
        require(target.viaSlice(hex"0102") == 2, "viaSlice");
    }

    function testViaRecursion() public view {
        require(target.viaRecursion(xs3()) == 12, "viaRecursion");
    }
}
