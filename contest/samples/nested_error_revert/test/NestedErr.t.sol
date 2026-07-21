// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {NestedErr} from "../src/NestedErr.sol";

// Plain try/catch (no forge-std): asserts the REAL solc+EVM revert — f() must
// revert with Nested([[1,2],[3]], "xy"), selector + ABI-encoded args
// byte-for-byte. Passes on real EVM.
contract NestedErrTest {
    function test_f_reverts_with_nested_dynamic_error() public {
        NestedErr c = new NestedErr();
        try c.f() {
            require(false, "expected revert");
        } catch (bytes memory data) {
            uint256[][] memory m = new uint256[][](2);
            m[0] = new uint256[](2);
            m[0][0] = 1;
            m[0][1] = 2;
            m[1] = new uint256[](1);
            m[1][0] = 3;
            bytes memory expected =
                abi.encodeWithSelector(NestedErr.Nested.selector, m, "xy");
            require(keccak256(data) == keccak256(expected),
                    "revert data must equal Nested([[1,2],[3]], 'xy')");
        }
    }
}
