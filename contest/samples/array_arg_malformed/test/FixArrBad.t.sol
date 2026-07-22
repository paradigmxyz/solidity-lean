// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {FixArrBad} from "../src/FixArrBad.sol";
contract FixArrBadTest {
    function test_total() public {
        require(new FixArrBad().total([uint256(1), 2, 3]) == 6, "t");
    }
}
