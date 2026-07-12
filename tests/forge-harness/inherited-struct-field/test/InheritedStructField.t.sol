// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {InheritedStructFieldTarget, StructBaseSelf, StructTypeFromBase} from "../src/InheritedStructField.sol";

contract InheritedStructFieldForgeTest {
    function testInheritedStructFieldAccess() public {
        InheritedStructFieldTarget target = new InheritedStructFieldTarget();

        target.setA(42);
        require(target.getA() == 42, "getA");
        require(target.getViaCopy() == 42, "copy");

        target.addItem(7, 41);
        target.bumpItem(7);
        require(target.itemAmount(7) == 42, "item");

        target.pushArr(42);
        require(target.firstA() == 42, "arr");
    }

    function testControls() public {
        StructBaseSelf base = new StructBaseSelf();
        base.setA(42);
        require(base.getA() == 42, "baseSelf");

        StructTypeFromBase derived = new StructTypeFromBase();
        derived.setOwn(42);
        require(derived.getOwn() == 42, "typeFromBase");
    }
}
