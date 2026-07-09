// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Emptier} from "../src/Emptier.sol";

// Asserts the REAL solc+EVM behavior: f() reverts with EMPTY data (0 bytes).
contract EmptierTest {
    function test_empty_revert() public {
        Emptier p = new Emptier();
        try p.f() returns (uint256) {
            require(false, "expected revert");
        } catch (bytes memory data) {
            require(data.length == 0, "must revert with empty data");
        }
    }
}
