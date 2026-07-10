// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Emitter} from "../src/Emitter.sol";
contract EmitterForgeTest {
    Emitter private target = new Emitter();
    function testRuns() public {
        target.f();
    }
}
