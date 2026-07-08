// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Snd} from "../src/Snd.sol";

contract SndForgeTest {
    Snd private target = new Snd();

    function testRunIsReal() public view {
        require(target.run() == 5, "run() should be 5");
    }
}
