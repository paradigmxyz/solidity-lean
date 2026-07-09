// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {ArrRet} from "../src/ArrRet.sol";
contract ArrRetTest { function test_vals() public { require(new ArrRet().vals().length == 3, "l"); } }
