// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {UninitializedFnPtrComparisonTarget} from "../src/UninitializedFnPtrComparison.sol";

contract UninitializedFnPtrComparisonTest {
    function testComparisonUsesZeroValue() public {
        UninitializedFnPtrComparisonTarget target =
            new UninitializedFnPtrComparisonTarget();
        (bool same, bool diff, bool inv) = target.equal();
        require(!same && !diff && !inv, "comparison");
    }

    function testCallingZeroPointerStillPanics() public {
        UninitializedFnPtrComparisonTarget target =
            new UninitializedFnPtrComparisonTarget();
        (bool ok, bytes memory data) =
            address(target).call(
                abi.encodeCall(UninitializedFnPtrComparisonTarget.callInvalid, ())
            );
        require(!ok, "call unexpectedly succeeded");
        require(data.length == 36, "panic payload length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(data, 32))
            code := mload(add(data, 36))
        }
        require(selector == 0x4e487b71 && code == 0x51, "wrong panic");
    }
}
