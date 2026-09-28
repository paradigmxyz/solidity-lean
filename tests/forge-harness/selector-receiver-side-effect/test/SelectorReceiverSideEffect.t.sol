// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import {SelectorReceiverSideEffect} from "../src/SelectorReceiverSideEffect.sol";

contract SelectorReceiverSideEffectTest {
    function testDiscardedSelectorStillEvaluatesReceiver() public {
        SelectorReceiverSideEffect target = new SelectorReceiverSideEffect();
        require(target.f() == 42, "receiver was not evaluated");
        require(target.x() == 42, "receiver side effect was not stored");
    }

    function testReturnedSelectorStillEvaluatesReceiver() public {
        SelectorReceiverSideEffect target = new SelectorReceiverSideEffect();
        require(
            target.selectorValue() == uint32(target.f.selector),
            "wrong selector value"
        );
        require(target.x() == 42, "return receiver side effect was not stored");
    }
}
