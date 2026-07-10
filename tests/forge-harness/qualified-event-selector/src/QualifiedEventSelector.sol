// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

library L {
    event Ping(uint256 x);
}

contract Base {
    event Ev(uint256 x);
}

contract QualifiedEventSelectorTarget is Base {
    // Same NAME as library L's event, DIFFERENT signature — the collision that
    // used to mis-target the by-name event-selector table (#137 `.selector`).
    event Ping(address a);

    // Bare own/inherited event `.selector` (topic0) — must stay unchanged.
    function ownEv() external pure returns (bytes32) {
        return Ev.selector;
    }

    function ownPing() external pure returns (bytes32) {
        return Ping.selector;
    }

    // Type-qualified event `.selector` (was OVER-REJECTED by the model):
    // resolves to the DECLARING scope's topic0, path-qualified so the L.Ping
    // collision cannot mis-target the contract's own Ping(address).
    function baseEv() external pure returns (bytes32) {
        return Base.Ev.selector;
    }

    function libPing() external pure returns (bytes32) {
        return L.Ping.selector;
    }
}
