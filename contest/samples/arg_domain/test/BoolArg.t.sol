// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {BoolArg} from "../src/BoolArg.sol";
contract BoolArgTest { function test_f() public { require(new BoolArg().f(true) == 1, "b"); } }
