// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/TupleDestructure.sol";

contract TupleDestructureForgeTest {
    function testDirectPair() public {
        TupleDestructureHarnessTarget target =
            new TupleDestructureHarnessTarget();

        (uint256 left, uint256 right) = target.directPair(4);

        require(left == 7, "left");
        require(right == 8, "right");
    }

    function testDestructureCall() public {
        TupleDestructureHarnessTarget target =
            new TupleDestructureHarnessTarget();

        require(target.destructureCall(4) == 56, "call");
    }

    function testLiteralHole() public {
        TupleDestructureHarnessTarget target =
            new TupleDestructureHarnessTarget();

        require(target.literalHole(10) == 1012, "hole");
    }

    function testSwap() public {
        TupleDestructureHarnessTarget target =
            new TupleDestructureHarnessTarget();

        require(target.swap(10) == 120, "swap");
    }
}
