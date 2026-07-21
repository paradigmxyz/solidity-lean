// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {NestedRet} from "../src/NestedRet.sol";

// Plain require-based test (no forge-std): asserts the REAL solc+EVM return
// values of vals() element-by-element. Passes on real EVM.
contract NestedRetTest {
    function test_vals_nested_dynamic() public {
        NestedRet c = new NestedRet();
        (uint256[][] memory m, bytes[] memory b) = c.vals();
        require(m.length == 2 && m[0].length == 2 && m[1].length == 1, "shape");
        require(m[0][0] == 1 && m[0][1] == 2 && m[1][0] == 3, "matrix values");
        require(b.length == 2, "bytes[] length");
        require(keccak256(b[0]) == keccak256(hex"aa"), "b[0]");
        require(keccak256(b[1]) == keccak256(hex"bbcc"), "b[1]");
    }
}
