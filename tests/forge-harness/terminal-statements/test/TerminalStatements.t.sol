// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TerminalStatementsHarnessTarget} from "../src/TerminalStatements.sol";

contract TerminalStatementsForgeTest {
    TerminalStatementsHarnessTarget private target =
        new TerminalStatementsHarnessTarget();

    function testExplicitReturn() public view {
        (uint256 first, uint256 second) = target.explicitReturn(4);
        require(first == 4, "first");
        require(second == 5, "second");
    }

    function testNamedFallthrough() public view {
        require(target.namedFallthrough(4) == 6, "fallthrough");
    }

    function testRevertString() public {
        try target.revertString() {
            revert("expected revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("terminal")),
                "reason"
            );
        }
    }

    function testRevertCustomNamedArgs() public {
        try target.revertCustom(7) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                TerminalStatementsHarnessTarget.Pair.selector,
                uint256(7),
                uint256(8)
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }

    function testSelfdestructStopsBeforeWrite() public {
        target.destroy(payable(address(0xbeef)));
        require(target.x() == 0, "write after selfdestruct");
    }
}
