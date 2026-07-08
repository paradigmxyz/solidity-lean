// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {EnvT} from "../src/EnvT.sol";
contract EnvTForgeTest {
    EnvT private target = new EnvT();
    function testTs() public view { require(target.ts() == 1, "ts==1 default"); }
}
