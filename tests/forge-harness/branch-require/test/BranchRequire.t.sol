// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {BranchRequireHarnessTarget} from "../src/BranchRequire.sol";

contract BranchRequireForgeTest {
    BranchRequireHarnessTarget private target =
        new BranchRequireHarnessTarget();

    function testChooseThenBranch() public {
        target.choose(4);
        require(target.read() == 4, "then branch");
    }

    function testChooseElseBranch() public {
        target.choose(40);
        require(target.read() == 10, "else branch");
    }

    function testRequireSmallReturns() public view {
        require(target.requireSmall(4) == 5, "require small");
    }

    function testRequireLargeReverts() public {
        try target.requireSmall(40) returns (uint256) {
            revert("expected revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("too large")),
                "reason"
            );
        }
    }

    function testAssertSmallReturns() public view {
        require(target.assertSmall(4) == 5, "assert small");
    }

    function testAssertLargePanics() public {
        try target.assertSmall(40) returns (uint256) {
            revert("expected panic");
        } catch Panic(uint256 code) {
            require(code == 0x01, "assert panic");
        }
    }

    function testAssertRollback() public {
        target.choose(4);

        try target.assertAndWrite(false) returns (uint256) {
            revert("expected panic");
        } catch Panic(uint256 code) {
            require(code == 0x01, "rollback panic");
        }

        require(target.read() == 4, "rollback");
        require(target.assertAndWrite(true) == 7, "assert write");
        require(target.read() == 7, "write committed");
    }
}
