// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {StrReturn} from "../src/StrReturn.sol";

// Asserts the REAL solc+EVM string return byte-for-byte.
contract StrReturnTest {
    function test_f_returns_delimiter_laden_string() public {
        StrReturn t = new StrReturn();
        require(
            keccak256(bytes(t.f())) == keccak256(bytes("a|b:c##EVT##d")),
            "string return must equal 'a|b:c##EVT##d'");
    }
}
