// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {StructDynArg} from "../src/StructDynArg.sol";
contract StructDynArgTest {
    function test_probe() public {
        uint256[] memory xs = new uint256[](2);
        xs[0] = 4; xs[1] = 5;
        StructDynArg.D memory d = StructDynArg.D(9, hex"deadbeef", xs);
        (uint256 v, bytes memory b) = new StructDynArg().probe(d);
        require(v == 17 && b.length == 4, "probe");
    }
}
