// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {ArrArg} from "../src/ArrArg.sol";
contract ArrArgTest {
    function test_sum() public {
        uint256[] memory xs = new uint256[](3);
        xs[0] = 7; xs[1] = 8; xs[2] = 9;
        (uint256 s, uint256 n) = new ArrArg().sum(xs);
        require(s == 24 && n == 3, "sum");
    }
}
