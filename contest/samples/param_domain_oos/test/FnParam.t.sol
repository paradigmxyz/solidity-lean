// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {FnParam} from "../src/FnParam.sol";
contract FnParamTest {
    function test_useB() public {
        require(new FnParam().useB(0x01020304) == 1, "a");
    }
}
