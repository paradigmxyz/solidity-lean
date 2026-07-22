// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {StructRet} from "../src/StructRet.sol";

// Plain require-based test (no forge-std): asserts the REAL solc+EVM struct
// return field-by-field. Passes on real EVM.
contract StructRetTest {
    function test_pack_struct_return() public {
        StructRet c = new StructRet();
        StructRet.Pack memory p = c.pack();
        require(p.a == 5, "a");
        require(keccak256(p.b) == keccak256(hex"4142"), "b");
        require(p.c.length == 1 && p.c[0] == 9, "c");
        require(p.fx[0] == 1 && p.fx[1] == 2, "fx");
        require(p.i.v == 3, "inner");
    }
}
