// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Pass} from "../src/Pass.sol";

contract PassForgeTest {
    Pass private target = new Pass();

    function testPassthroughIsReal() public view {
        require(target.f(200) == 200, "f(200) should be 200");
    }
}
