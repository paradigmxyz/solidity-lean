// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CustomErrorHarnessTarget} from "../src/CustomError.sol";

contract CustomErrorForgeTest {
    CustomErrorHarnessTarget private target =
        new CustomErrorHarnessTarget();

    function testCheckReturns() public view {
        require(target.check(4) == 5, "check");
    }

    function testCheckCustomError() public {
        try target.check(20) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                CustomErrorHarnessTarget.TooBig.selector,
                uint256(20),
                uint256(10)
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }

    function testNamedCustomError() public {
        try target.named(7) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                CustomErrorHarnessTarget.PairBad.selector,
                uint256(7),
                uint256(9)
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }
}
