// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExternalSelfCallTarget, ExternalSelfCallCtor} from "../src/ExternalSelfCall.sol";

contract ExternalSelfCallForgeTest {
    ExternalSelfCallTarget private target = new ExternalSelfCallTarget();

    function testValueRead() public {
        require(target.h() == 5, "self-call value read");
    }

    function testMutationPersists() public {
        require(target.doInc() == 1, "self-call mutation 1");
        require(target.doInc() == 2, "self-call mutation 2");
        require(target.counter() == 2, "self-call mutation persisted");
    }

    function testSenderIdentity() public {
        require(target.senderCheck(), "self-call msg.sender == address(this)");
    }

    function testTryCatchRoutes() public {
        require(target.tryCatchBoom() == 42, "reverting self-call routes to catch");
    }

    function testLowLevelFalse() public {
        require(!target.lowLevelBoom(), "low-level reverting self-call => false");
    }

    function testConstructorSelfCallReverts() public {
        try new ExternalSelfCallCtor() returns (ExternalSelfCallCtor) {
            require(false, "constructor self-call should revert deploy");
        } catch {}
    }
}
