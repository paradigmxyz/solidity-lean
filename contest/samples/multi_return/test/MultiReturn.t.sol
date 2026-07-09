// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {MultiReturn} from "../src/MultiReturn.sol";

// Asserts the REAL solc+EVM observable of the mixed-scalar multi-return.
contract MultiReturnTest {
    function test_f_returns_mixed_scalars() public {
        MultiReturn t = new MultiReturn();
        (int256 a, uint128 b, address c, bytes4 d) = t.f();
        require(a == -7, "a");
        require(b == 42, "b");
        require(c == address(0x0000000000000000000000000000000000001234), "c");
        require(d == bytes4(0xAABBCCDD), "d");
    }
}
