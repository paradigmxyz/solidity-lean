// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out acceptance contract (no hand-written proofs): a mapping of flags with a counter,
/// an owner check and an event; straight-line code, no external calls.
/// @custom:ghost uint256 listedCount
/// @custom:invariant count == listedCount
contract Registry {
    mapping(address => bool) public listed;
    uint256 public count;
    address public owner;

    event Listed(address indexed who, bool on);

    /// @custom:ensures owner == msg.sender && count == 0
    constructor() {
        owner = msg.sender;
    }

    /// @custom:requires msg.sender == owner && !listed[who]
    /// @custom:ensures listed[who] && count == old(count) + 1
    /// @custom:ensures forall address a :: a != who ==> listed[a] == old(listed[a])
    function add(address who) external {
        require(msg.sender == owner, "owner");
        require(!listed[who], "listed");
        listed[who] = true;
        /// @custom:ghost listedCount = listedCount + 1
        count = count + 1;
        emit Listed(who, true);
    }

    /// @custom:requires msg.sender == owner && listed[who]
    /// @custom:ensures !listed[who] && count == old(count) - 1
    /// @custom:ensures forall address a :: a != who ==> listed[a] == old(listed[a])
    function remove(address who) external {
        require(msg.sender == owner, "owner");
        require(listed[who], "not listed");
        listed[who] = false;
        /// @custom:ghost listedCount = listedCount - 1
        count = count - 1;
        emit Listed(who, false);
    }
}
