// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {OwnerC} from "../src/OwnerC.sol";
contract OwnerCTest { function test_owner() public { new OwnerC(); } }
