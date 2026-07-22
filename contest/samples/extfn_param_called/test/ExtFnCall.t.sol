// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {ExtFnCall} from "../src/ExtFnCall.sol";
contract ExtFnCallTest {
    function probe() external pure returns (uint256) { return 7; }
    function test_useCb() public {
        ExtFnCall c = new ExtFnCall();
        require(c.useCb(this.probe) == 7, "call");
    }
}
