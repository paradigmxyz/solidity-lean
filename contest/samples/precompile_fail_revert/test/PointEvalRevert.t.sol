// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {PointEvalRevert} from "../src/PointEvalRevert.sol";

contract PointEvalRevertTest {
    function test_entry_reverts_failed() public {
        PointEvalRevert c = new PointEvalRevert();
        (bool ok, bytes memory ret) = address(c).call(abi.encodeCall(PointEvalRevert.f, ()));
        require(!ok, "expected a revert");
        require(keccak256(ret) == keccak256(abi.encodeWithSelector(
            PointEvalRevert.Failed.selector, false, uint256(0))), "expected Failed(false, 0)");
    }
}
