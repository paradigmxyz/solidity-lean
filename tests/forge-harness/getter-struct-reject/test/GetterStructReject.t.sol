// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {GetterStructRejectHarnessTarget} from "../src/GetterStructReject.sol";

contract GetterStructRejectForgeTest {
    GetterStructRejectHarnessTarget private target =
        new GetterStructRejectHarnessTarget();

    // Accepted-control getter: mapping + array dropped, value + string kept,
    // nested pure-value struct returned whole.
    function testControlGetterOmitsMappingAndArrayKeepsRest() public {
        target.setup(11, "hi", 5, 6);

        (uint256 keep, string memory label, GetterStructRejectHarnessTarget.Inner memory inner) =
            target.s();

        require(keep == 11, "keep");
        require(
            keccak256(bytes(label)) == keccak256(bytes("hi")),
            "label"
        );
        require(inner.a == 5, "inner.a");
        require(inner.b == 6, "inner.b");
    }
}
