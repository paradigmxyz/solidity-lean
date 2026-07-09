// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Regression guard: the constructor records msg.sender. The EVM deploy must be
// pranked to the canonical sender (measure.py) so the ctor sees the SAME sender
// Solidus threads into constructWithContext — otherwise owner would be the test
// harness address on the EVM side and diverge spuriously.
contract OwnerC {
    address public owner;   // slot 0
    constructor() { owner = msg.sender; }
    function getOwner() external view returns (address) { return owner; }
}
