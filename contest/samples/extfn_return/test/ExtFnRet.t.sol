// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {ExtFnRet} from "../src/ExtFnRet.sol";
contract ExtFnRetTest {
    function test_get() public {
        ExtFnRet c = new ExtFnRet();
        function() external pure returns (uint256) f = c.get();
        require(f.selector == c.probe.selector, "sel");
        require(f.address == address(c), "addr");
        require(f() == 7, "call");
    }
}
