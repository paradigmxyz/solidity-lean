// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {PointEvalOog} from "../src/PointEvalOog.sol";

contract PointEvalOogTest {
    function test_entry_runs_out_of_gas() public {
        PointEvalOog c = new PointEvalOog();
        (bool ok, bytes memory ret) = address(c).call(abi.encodeCall(PointEvalOog.f, ()));
        require(!ok && ret.length == 0, "expected an empty out-of-gas revert");
    }
}
