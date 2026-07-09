// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Reverter, Bad} from "../src/Reverter.sol";

// Plain try/catch (no forge-std): asserts the REAL solc+EVM revert — f() must
// revert with the custom error Bad(42, true), i.e. selector + ABI-encoded args
// byte-for-byte. Passes on real EVM.
contract ReverterTest {
    function test_f_reverts_with_scalar_custom_error() public {
        Reverter r = new Reverter();
        try r.f() {
            require(false, "expected revert");
        } catch (bytes memory data) {
            bytes memory expected =
                abi.encodeWithSelector(Bad.selector, uint256(42), true);
            require(keccak256(data) == keccak256(expected),
                    "revert data must equal Bad(42, true)");
        }
    }
}
