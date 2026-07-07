// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {
    ReentrancyAdoptionVictim,
    ReentrancyAdoptionChild,
    ReentrancyAdoptionAttacker
} from "../src/ReentrancyAdoption.sol";

interface Vm {
    function store(address t, bytes32 slot, bytes32 value) external;
    function deal(address who, uint256 amount) external;
}

contract ReentrancyAdoptionForgeTest {
    Vm internal constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function newPair()
        internal
        returns (ReentrancyAdoptionVictim, ReentrancyAdoptionAttacker)
    {
        ReentrancyAdoptionAttacker attacker = new ReentrancyAdoptionAttacker();
        ReentrancyAdoptionVictim victim =
            new ReentrancyAdoptionVictim(address(attacker));
        attacker.setVictim(payable(address(victim)));
        return (victim, attacker);
    }

    // Lane 1: reentrant storage write.
    function testReentrantStorageWrite() public {
        (ReentrancyAdoptionVictim victim,) = newPair();
        uint256 ret = victim.pull();
        require(ret == 42, "pull return");
        require(victim.x() == 42, "x adopted");
    }

    // Lane 2: reentrant ill-encoded word then typed read. The environment
    // (here, the test acting as the reentering world) plants a non-canonical
    // bool (2 -> truthy) and enum (7 -> out of range) into the victim's
    // storage. Getter reads must be TOTAL: bool getter true, enum getter
    // reverts Panic(0x21).
    function testReentrantIllEncodedThenRead() public {
        (ReentrancyAdoptionVictim victim,) = newPair();
        // flag lives alone in slot 1, choice alone in slot 3.
        vm.store(address(victim), bytes32(uint256(1)), bytes32(uint256(2)));
        vm.store(address(victim), bytes32(uint256(3)), bytes32(uint256(7)));
        require(victim.flag(), "flag truthy on 2");
        (bool ok, bytes memory data) = address(victim).staticcall(
            abi.encodeWithSignature("choice()")
        );
        require(!ok, "enum getter reverts");
        require(data.length == 36, "panic payload length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(data, 0x20))
            code := mload(add(data, 0x24))
        }
        require(selector == bytes4(0x4e487b71), "panic selector");
        require(code == 0x21, "panic 0x21");
    }

    // Lane 3: balance-changing callee. Victim funded with 100; spends 40; the
    // callee refunds 20. Final victim balance = 100 - 40 + 20 = 80.
    function testBalanceChangingCallee() public {
        (ReentrancyAdoptionVictim victim,) = newPair();
        vm.deal(address(victim), 100);
        uint256 ret = victim.spend(40);
        require(ret == 80, "spend return balance");
        require(address(victim).balance == 80, "victim balance adopted");
    }

    // Lane 4: transient storage mutation across reentry. tk := 1; callee
    // reenters bump() -> tk := 2; observed after the call.
    function testTransientMutation() public {
        (ReentrancyAdoptionVictim victim,) = newPair();
        uint256 ret = victim.transientRoundTrip();
        require(ret == 2, "transient adopted");
    }

    // Lane 5: create-with-reentry. Child constructor reenters setX(7).
    function testCreateWithReentry() public {
        (ReentrancyAdoptionVictim victim,) = newPair();
        uint256 ret = victim.deploy();
        require(ret == 7, "deploy return");
        require(victim.x() == 7, "x set by child constructor");
    }
}
