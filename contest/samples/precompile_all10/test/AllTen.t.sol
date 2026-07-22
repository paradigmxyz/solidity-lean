// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {AllTen} from "../src/AllTen.sol";
contract AllTenTest {
    function test_run() public {
        (, uint256 okBits) = new AllTen().run(7);
        require(okBits == 1023, "all ten precompiles must answer");
    }
}
