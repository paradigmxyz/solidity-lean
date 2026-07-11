// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NewContractLocalStructArrayHarness} from "../src/NewContractLocalStructArray.sol";

contract NewContractLocalStructArrayForgeTest {
    NewContractLocalStructArrayHarness private harness =
        new NewContractLocalStructArrayHarness();

    // G: local var of a contract-local struct array.
    function testLocalVarLen() public view {
        require(harness.localVarLen() == 3, "local struct array local var length");
    }

    // G2: return of a contract-local struct array.
    function testReturnArr() public view {
        require(harness.returnArr().length == 1, "local struct array return length");
    }

    // G3: multi-field local struct array.
    function testMultiLen() public view {
        require(harness.multiLen() == 2, "multi-field local struct array length");
    }

    // G4: array-of-array of the local struct.
    function testArr2Len() public view {
        require(harness.arr2Len() == 4, "array-of-array of local struct length");
    }

    // H: elementary element array.
    function testUintLen() public view {
        require(harness.uintLen() == 5, "uint array length");
    }
}
