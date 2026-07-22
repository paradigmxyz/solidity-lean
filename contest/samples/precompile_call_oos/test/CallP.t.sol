// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {CallP} from "../src/CallP.sol";
contract CallPTest {
    function test_run() public {
        require(new CallP().run(7), "evm call to precompile succeeds");
    }
}
