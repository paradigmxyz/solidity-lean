// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {CustomErrorDynamicHarnessTarget} from "../src/CustomErrorDynamic.sol";

contract CustomErrorDynamicForgeTest {
    CustomErrorDynamicHarnessTarget private target =
        new CustomErrorDynamicHarnessTarget();

    function testDynamicCustomErrorPayload() public {
        string memory reason = "cat";
        bytes memory payload = hex"010203";

        try target.failDynamic(reason, payload) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                CustomErrorDynamicHarnessTarget.DynamicBad.selector,
                reason,
                payload
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }

    function testStructCustomErrorPayload() public {
        uint256 code = 7;
        bytes memory payload = hex"0405";

        try target.failStruct(code, payload) {
            revert("expected revert");
        } catch (bytes memory data) {
            CustomErrorDynamicHarnessTarget.Detail memory detail =
                CustomErrorDynamicHarnessTarget.Detail({
                    code: code,
                    payload: payload
                });
            bytes memory expected = abi.encodeWithSelector(
                CustomErrorDynamicHarnessTarget.StructBad.selector,
                detail
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }
}
