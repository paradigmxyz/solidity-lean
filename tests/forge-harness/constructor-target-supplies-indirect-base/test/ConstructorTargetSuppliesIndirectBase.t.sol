// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import { Target } from "../src/ConstructorTargetSuppliesIndirectBase.sol";

contract ConstructorTargetSuppliesIndirectBaseForgeTest {
    // Target supplies its INDIRECT base Base(3, 4) via a constructor modifier,
    // while the direct inheritor Mid supplies nothing. Base's two arguments must
    // still be found and bound: a == 3, b == 4, and Mid's own constructor runs
    // (m == 7).
    function testTargetSuppliesIndirectBase() public {
        Target t = new Target();
        require(t.a() == 3, "a from Target(Base(3,4))");
        require(t.b() == 4, "b from Target(Base(3,4))");
        require(t.m() == 7, "m from Mid constructor");
    }
}
