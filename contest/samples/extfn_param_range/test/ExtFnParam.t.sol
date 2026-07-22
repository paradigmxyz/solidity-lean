// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {ExtFnParam} from "../src/ExtFnParam.sol";
contract ExtFnParamTest {
    function probe() external pure returns (uint256) { return 7; }
    function test_inspect() public {
        ExtFnParam c = new ExtFnParam();
        (address a, bytes4 s) = c.inspect(this.probe);
        require(a == address(this), "addr");
        require(s == this.probe.selector, "sel");
    }
}
