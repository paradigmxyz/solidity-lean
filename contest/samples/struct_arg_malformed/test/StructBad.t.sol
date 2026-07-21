// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {StructBad} from "../src/StructBad.sol";
contract StructBadTest {
    function test_join() public {
        require(new StructBad().join(StructBad.Q(1, 200)) == 201, "j");
    }
}
