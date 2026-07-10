// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    RequireCustomErrorHarnessTarget,
    FreeErr
} from "../src/RequireCustomError.sol";

// REQUIRE-CUSTOM-ERROR (#120): solc 0.8.26+ accepts a custom-error instance as
// require's second argument. On a false condition it reverts with the error's
// selector ++ abi.encode(args), identically whether the error is declared at
// CONTRACT level or FILE level (free error). These tests pin the real
// solc/EVM revert bytes for both scopes so the Lean model can be compared.
contract RequireCustomErrorForgeTest {
    RequireCustomErrorHarnessTarget private target =
        new RequireCustomErrorHarnessTarget();

    // Contract-level error in require: passing condition returns the argument.
    function testCReturns() public view {
        require(target.c(5) == 5, "c");
    }

    // c(0): require(cond, MemberErr(a)) with a CONTRACT-level declared error
    // reverts with the custom selector ++ abi.encode(a), NOT Error(string).
    function testCContractLevelCustomError() public {
        try target.c(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                RequireCustomErrorHarnessTarget.MemberErr.selector,
                uint256(0)
            );
            require(keccak256(data) == keccak256(expected), "c-data");
        }
    }

    // Free (file-level) error in require: passing condition returns the arg.
    function testFrReturns() public view {
        require(target.fr(7) == 7, "fr");
    }

    // fr(0): require(cond, FreeErr(a)) with a FILE-level declared error reverts
    // with the free error's selector ++ abi.encode(a), identically to the
    // contract-level case.
    function testFrFreeLevelCustomError() public {
        try target.fr(0) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSelector(FreeErr.selector, uint256(0));
            require(keccak256(data) == keccak256(expected), "fr-data");
        }
    }
}
