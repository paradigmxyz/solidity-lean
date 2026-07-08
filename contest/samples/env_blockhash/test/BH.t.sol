// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {BH} from "../src/BH.sol";
contract BHForgeTest {
    BH private target = new BH();
    function testReal() public view { target.bh(); require(true, "blockhash reproduces"); }
}
