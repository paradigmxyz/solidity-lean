// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Outside the envelope: a value call with the state written after it (reentrant withdraw).
/// Expected: BLOCKED (external call / value transfer).
contract Reentrancy {
    mapping(address => uint256) public balance;

    /// @custom:ensures balance[msg.sender] == 0
    function withdraw() external {
        uint256 b = balance[msg.sender];
        (bool ok, ) = msg.sender.call{value: b}("");
        require(ok, "send");
        balance[msg.sender] = 0;
    }
}
