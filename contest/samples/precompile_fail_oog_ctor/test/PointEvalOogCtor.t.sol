// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {PointEvalOogCtor} from "../src/PointEvalOogCtor.sol";

contract PointEvalOogCtorTest {
    function test_deploy_runs_out_of_gas() public {
        try new PointEvalOogCtor() returns (PointEvalOogCtor) {
            revert("deploy should have run out of gas");
        } catch (bytes memory data) {
            require(data.length == 0, "expected empty revert data");
        }
    }
}
