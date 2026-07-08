// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageUninitFnPtrHarnessTarget} from "../src/StorageUninitFnPtr.sol";

// Forge ground truth for G17: calling an uninitialized STORAGE internal
// function pointer panics 0x51.
contract StorageUninitFnPtrForgeTest {
    function newTarget() internal returns (StorageUninitFnPtrHarnessTarget) {
        // assign = false: leaves both storage pointers at their zero default.
        return new StorageUninitFnPtrHarnessTarget(false);
    }

    function expectPanic51(bytes memory ret, bool ok) internal pure {
        require(!ok, "must revert");
        require(ret.length == 36, "panic data length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(ret, 32))
            code := mload(add(ret, 36))
        }
        require(selector == 0x4e487b71, "panic selector");
        require(code == 0x51, "panic code 0x51");
    }

    function testStorageDefaultPanics51() public {
        StorageUninitFnPtrHarnessTarget target = newTarget();
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature("callStored(uint256)", uint256(7))
        );
        expectPanic51(ret, ok);
    }

    function testCtorUnsetPanics51() public {
        StorageUninitFnPtrHarnessTarget target = newTarget();
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature("callCtor(uint256)", uint256(9))
        );
        expectPanic51(ret, ok);
    }
}
