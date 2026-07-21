// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorRevertEmpty} from "../src/CtorRevertEmpty.sol";

contract CtorRevertEmptyTest {
    function test_deploy_reverts_empty() public {
        try new CtorRevertEmpty() returns (CtorRevertEmpty) {
            revert("deploy should have reverted");
        } catch (bytes memory data) {
            require(data.length == 0, "expected empty revert data");
        }
    }
}
