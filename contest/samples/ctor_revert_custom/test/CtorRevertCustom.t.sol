// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorRevertCustom} from "../src/CtorRevertCustom.sol";

contract CtorRevertCustomTest {
    function test_deploy_reverts_custom() public {
        try new CtorRevertCustom(42) returns (CtorRevertCustom) {
            revert("deploy should have reverted");
        } catch (bytes memory data) {
            require(data.length == 4 + 32, "wrong revert data length");
            require(bytes4(data) == CtorRevertCustom.CtorBad.selector,
                    "wrong selector");
        }
    }
}
