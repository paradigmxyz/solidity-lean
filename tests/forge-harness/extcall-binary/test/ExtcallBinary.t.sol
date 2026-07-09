// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExtcallBinaryHarnessTarget} from "../src/ExtcallBinary.sol";

contract ExtcallBinaryForgeTest {
    ExtcallBinaryHarnessTarget private target = new ExtcallBinaryHarnessTarget();

    function testRequireGuardPasses() public view {
        require(target.requireGuard(address(0xBEEF), 50) == 50, "require guard pass");
    }

    function testRequireGuardReverts() public {
        try target.requireGuard(address(0xBEEF), 200) returns (uint256) {
            require(false, "require guard should revert");
        } catch {}
    }

    function testVarDeclInit() public view {
        require(target.varDeclInit() == 4, "var-decl init");
    }

    function testAssignRhs() public view {
        require(target.assignRhs() == 4, "assign rhs");
    }

    function testWhileCond() public view {
        require(target.whileCond() == 10, "while cond");
    }

    function testIfAndTrue() public view {
        require(target.ifAnd(true) == 1, "if-and true");
    }

    function testIfAndFalse() public view {
        require(target.ifAnd(false) == 0, "if-and false");
    }

    function testIfOrTrue() public view {
        require(target.ifOr(true) == 1, "if-or true");
    }

    function testIfOrFalse() public view {
        require(target.ifOr(false) == 1, "if-or false");
    }

    function testReturnBin() public view {
        require(target.returnBin(7) == 10, "return bin");
    }
}
