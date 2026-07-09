// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {BqcDerivedB, BqcDiamondD} from "../src/BaseQualifiedCall.sol";

contract BaseQualifiedCallForgeTest {
    function testLinearBaseQualifiedCall() public {
        BqcDerivedB derived = new BqcDerivedB();
        require(derived.viaBase() == 1, "viaBase must run base A body");
        require(derived.viaDyn() == 2, "viaDyn must run most-derived body");
    }

    function testDiamondExplicitBaseCalls() public {
        BqcDiamondD d = new BqcDiamondD();
        require(d.callA() == 10, "DA.g must be 10");
        require(d.callB() == 20, "DB.g must be 20");
        require(d.callC() == 30, "DC.g must be 30");
        require(d.callDyn() == 40, "dynamic g must be 40");
    }
}
