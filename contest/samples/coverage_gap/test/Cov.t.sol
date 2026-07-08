// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Cov} from "../src/Cov.sol";

contract CovForgeTest {
    Cov private target = new Cov();

    function testRunIsReal() public view {
        require(target.run() == 7, "run() should be 7");
    }
}
