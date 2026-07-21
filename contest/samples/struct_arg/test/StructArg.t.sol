// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {StructArg} from "../src/StructArg.sol";
contract StructArgTest {
    function test_join() public {
        require(new StructArg().join(StructArg.P(40, 2)) == 42, "join");
    }
}
