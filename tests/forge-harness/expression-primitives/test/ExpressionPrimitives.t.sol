// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ExpressionPrimitives.sol";

contract ExpressionPrimitivesForgeTest {
    function testUpdateDeleteAndIncDec() public {
        ExpressionPrimitivesHarnessTarget target =
            new ExpressionPrimitivesHarnessTarget();

        require(target.update(9) == 9, "update");
        require(target.value() == 0, "delete");
    }

    function testUnaryOps() public {
        ExpressionPrimitivesHarnessTarget target =
            new ExpressionPrimitivesHarnessTarget();

        (bool inverted, int256 negated, uint256 bitNot) =
            target.unary(false, 7);
        require(inverted, "logical");
        require(negated == -7, "neg");
        require(bitNot == type(uint256).max, "bitnot");
    }

    function testInlineArrayLiteral() public {
        ExpressionPrimitivesHarnessTarget target =
            new ExpressionPrimitivesHarnessTarget();

        require(target.arrayPick() == 2, "array");
    }

    function testGlobalPrimitiveBuiltins() public {
        ExpressionPrimitivesHarnessTarget target =
            new ExpressionPrimitivesHarnessTarget();

        (uint256 sumMod, uint256 productMod, bytes32 digest) =
            target.modularArithmetic();
        require(sumMod == 2, "addmod");
        require(productMod == 5, "mulmod");
        require(digest == keccak256(hex"010203"), "keccak");
        require(target.addmodZero(5) == 3, "addmod nonzero");
        require(target.mulmodZero(5) == 2, "mulmod nonzero");
    }

    function testModularArithmeticZeroModulusPanics() public {
        ExpressionPrimitivesHarnessTarget target =
            new ExpressionPrimitivesHarnessTarget();

        try target.addmodZero(0) returns (uint256) {
            revert("addmod zero accepted");
        } catch Panic(uint256 code) {
            require(code == 0x12, "addmod panic");
        }

        try target.mulmodZero(0) returns (uint256) {
            revert("mulmod zero accepted");
        } catch Panic(uint256 code) {
            require(code == 0x12, "mulmod panic");
        }
    }
}
