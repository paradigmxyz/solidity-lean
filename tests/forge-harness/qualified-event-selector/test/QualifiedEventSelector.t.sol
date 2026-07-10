// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {QualifiedEventSelectorTarget, Base, L} from "../src/QualifiedEventSelector.sol";

contract QualifiedEventSelectorForgeTest {
    QualifiedEventSelectorTarget private target =
        new QualifiedEventSelectorTarget();

    function testOwnEvSelector() public view {
        require(target.ownEv() == keccak256("Ev(uint256)"), "ownEv");
    }

    function testOwnPingSelector() public view {
        require(target.ownPing() == keccak256("Ping(address)"), "ownPing");
    }

    function testBaseEvSelector() public view {
        require(target.baseEv() == keccak256("Ev(uint256)"), "baseEv");
        require(target.baseEv() == Base.Ev.selector, "baseEv const");
    }

    function testLibPingSelector() public view {
        // Path-qualified: resolves to L.Ping(uint256), NOT the contract's
        // own Ping(address).
        require(target.libPing() == keccak256("Ping(uint256)"), "libPing");
        require(target.libPing() == L.Ping.selector, "libPing const");
        require(target.libPing() != keccak256("Ping(address)"), "libPing collision");
    }
}
