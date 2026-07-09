// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: writes a mapping(address=>uint256) AND emits an event with
// an INDEXED address topic + a non-indexed uint. Exercises keccak-derived mapping
// storage-slot parity AND indexed/non-indexed event rendering together — the two
// surfaces most likely to expose a slot/topic asymmetry between the engines.
contract MapEvent {
    mapping(address => uint256) public balances;
    event Deposit(address indexed who, uint256 amount);

    function deposit(address who, uint256 amount) external {
        balances[who] = amount;
        emit Deposit(who, amount);
    }
}
