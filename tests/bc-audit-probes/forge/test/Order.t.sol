// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Order} from "../src/Order.sol";
contract OrderForgeTest {
    function testArg() public { Order o=new Order(); emit log_named_uint("argOrder", o.argOrder()); }
    function testAssign() public { Order o=new Order(); emit log_named_uint("assignOrder", o.assignOrder()); }
    event log_named_uint(string k, uint256 v);
}
