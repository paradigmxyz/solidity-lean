// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    QualifiedCalleeHarnessTarget,
    Base
} from "../src/QualifiedCallee.sol";

contract QualifiedCalleeForgeTest {
    QualifiedCalleeHarnessTarget private target =
        new QualifiedCalleeHarnessTarget();

    function testEmitBaseHit() public {
        target.emitBaseHit(4);
    }

    function testEmitSelfHit() public {
        target.emitSelfHit(9);
    }

    function testRevertBaseErr() public {
        try target.revertBaseErr(5) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSelector(Base.BaseErr.selector, uint256(5));
            require(keccak256(data) == keccak256(expected), "baseerr");
        }
    }

    function testRevertSelfErr() public {
        try target.revertSelfErr(6) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                QualifiedCalleeHarnessTarget.LocalErr.selector,
                uint256(6)
            );
            require(keccak256(data) == keccak256(expected), "selferr");
        }
    }

    function testRequireBaseErr() public {
        try target.requireBaseErr(0) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSelector(Base.BaseErr.selector, uint256(0));
            require(keccak256(data) == keccak256(expected), "requirebaseerr");
        }
    }
}
