// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Arith} from "../src/Arith.sol";

contract ArithForgeTest {
    Arith private target = new Arith();

    // Asserts the REAL solc+EVM observable: add(2, 3) == 5.
    function testAddIsReal() public view {
        require(target.add(2, 3) == 5, "add(2,3) should be 5");
    }
}
