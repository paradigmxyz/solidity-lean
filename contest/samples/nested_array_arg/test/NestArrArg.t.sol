// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {NestArrArg} from "../src/NestArrArg.sol";
contract NestArrArgTest {
    function test_pick() public {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](2); m[0][0] = 1; m[0][1] = 2;
        m[1] = new uint256[](1); m[1][0] = 3;
        (uint256 v, uint256 n) = new NestArrArg().pick(m);
        require(v == 5 && n == 2, "pick");
    }
}
