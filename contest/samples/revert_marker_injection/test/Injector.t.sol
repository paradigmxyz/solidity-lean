// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Injector} from "../src/Injector.sol";

// Asserts the REAL solc+EVM behavior: f() reverts with the exact marker-laden
// Error(string) reason, byte-for-byte.
contract InjectorTest {
    function test_marker_reason() public {
        Injector p = new Injector();
        try p.f() returns (uint256) {
            require(false, "expected revert");
        } catch (bytes memory data) {
            require(
                keccak256(data) == keccak256(abi.encodeWithSignature(
                    "Error(string)",
                    "a|b##EVT##c##STO##d revert|panic:99 success|w:5 revert|custom:X:1")),
                "must revert with the marker-laden reason");
        }
    }
}
