// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {InternalFnPointersHarnessTarget} from "../src/InternalFnPointers.sol";

// Forge ground truth for the stage-C internal-function-pointer pin.
contract InternalFnPointersForgeTest {
    function newTarget() internal returns (InternalFnPointersHarnessTarget) {
        return new InternalFnPointersHarnessTarget();
    }

    function testViaStorage() public {
        require(newTarget().viaStorage(true, 21) == 42, "viaStorage true");
        require(newTarget().viaStorage(false, 21) == 63, "viaStorage false");
    }

    function testViaParam() public {
        require(newTarget().viaParam(3) == 12, "viaParam");
    }

    function testViaReturn() public {
        require(newTarget().viaReturn(false, 10) == 30, "viaReturn");
    }

    function testUninitializedPanics51() public {
        InternalFnPointersHarnessTarget target = newTarget();
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature("callUninitialized(uint256)", uint256(5))
        );
        require(!ok, "must revert");
        // Panic(uint256) selector 0x4e487b71 with code 0x51.
        require(ret.length == 36, "panic data length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(ret, 32))
            code := mload(add(ret, 36))
        }
        require(selector == 0x4e487b71, "panic selector");
        require(code == 0x51, "panic code");
    }

    function testViaRecursion() public {
        require(newTarget().viaRecursion(7) == 7, "viaRecursion");
    }
}
