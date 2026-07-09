// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {AC} from "../src/AC.sol";
contract ACTest { function test_two() public { require(new AC().two(5, 6) == 11, "sum"); } }
