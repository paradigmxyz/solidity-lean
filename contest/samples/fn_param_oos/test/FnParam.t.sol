// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {FnParam} from "../src/FnParam.sol";
contract FnParamTest {
    function seven() external pure returns (uint256) { return 7; }
    function test_useCb() public {
        require(new FnParam().useCb(this.seven) == 1, "a");
    }
}
