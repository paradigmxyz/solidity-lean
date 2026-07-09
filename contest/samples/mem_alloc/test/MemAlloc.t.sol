// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {MemAlloc} from "../src/MemAlloc.sol";
contract MemAllocTest { function test_sum() public { require(new MemAlloc().sum(3) == 9, "s"); } }
