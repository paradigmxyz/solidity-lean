// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {InternalLibraryFnPtrValueTarget} from "../src/InternalLibraryFnPtrValue.sol";

contract InternalLibraryFnPtrValueTest {
    function testMemberAssignmentSucceeds() public {
        InternalLibraryFnPtrValueTarget target =
            new InternalLibraryFnPtrValueTarget();
        require(target.assignOnly() == 0, "assignment");
    }

    function testAssignedMemberCanBeCalled() public {
        InternalLibraryFnPtrValueTarget target =
            new InternalLibraryFnPtrValueTarget();
        require(target.assignAndCall() == 0, "dispatch");
    }
}
