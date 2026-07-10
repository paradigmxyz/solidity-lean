// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RequireFnReasonHarnessTarget} from "../src/RequireFnReason.sol";

contract RequireFnReasonForgeTest {
    RequireFnReasonHarnessTarget private target =
        new RequireFnReasonHarnessTarget();

    function testFReturns() public view {
        require(target.f(3) == 3, "f");
    }

    // f(0): require(cond, boom()) with a bare string-returning function call as
    // the reason must revert with Error(string) = "boom" (selector 0x08c379a0),
    // NOT a custom-error revert.
    function testFFnReasonError() public {
        try target.f(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSignature("Error(string)", "boom");
            require(keccak256(data) == keccak256(expected), "f-data");
        }
    }

    function testCReturns() public view {
        require(target.c(5) == 5, "c");
    }

    // c(0): require(cond, MyErr(x)) with a DECLARED error must still revert with
    // the custom selector ++ abi.encode(args).
    function testCCustomError() public {
        try target.c(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                RequireFnReasonHarnessTarget.MyErr.selector,
                uint256(0)
            );
            require(keccak256(data) == keccak256(expected), "c-data");
        }
    }

    // s(0): string local-variable reason -> Error(string) = "svar".
    function testSStringVarError() public {
        try target.s(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSignature("Error(string)", "svar");
            require(keccak256(data) == keccak256(expected), "s-data");
        }
    }

    function testSReturns() public view {
        require(target.s(4) == 4, "s");
    }

    // t(0): conditional (ternary) string reason -> Error(string) = "lo".
    function testTTernaryError() public {
        try target.t(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSignature("Error(string)", "lo");
            require(keccak256(data) == keccak256(expected), "t-data");
        }
    }

    function testTReturns() public view {
        require(target.t(9) == 9, "t");
    }
}
