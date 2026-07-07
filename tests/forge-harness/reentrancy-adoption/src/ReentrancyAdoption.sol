// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// Victim. Each entry makes ONE external call to an environment address; a real
/// reentering callee mutates the victim's own account (storage / balance /
/// transient / a child-create callback) and the victim observes the adopted
/// change after the call returns. The Lean side models each entry with a
/// PostDelta on the outgoing-call responder row, derived from Forge's trace.
contract ReentrancyAdoptionVictim {
    enum Choice {
        A,
        B,
        C
    }

    uint256 public x; // slot 0
    bool public flag; // slot 1 (byte 0)
    uint256 private _pad1; // slot 2 — keeps flag alone in slot 1
    Choice public choice; // slot 3 (byte 0)
    uint256 private _pad2; // slot 4 — keeps choice alone in slot 3
    address public callee; // slot 5
    uint256 transient tk; // transient slot 0

    constructor(address _callee) {
        callee = _callee;
    }

    receive() external payable {}

    // --- functions a reentering callee calls back into ---
    function setX(uint256 v) external {
        x = v;
    }

    // --- entrypoints that make the outgoing call ---

    // Lane 1: reentrant storage write. Callee reenters setX(42).
    function pull() external returns (uint256) {
        (bool ok,) = callee.call(abi.encodeWithSignature("notify()"));
        require(ok, "callee");
        return x;
    }

    // Lane 3: balance-changing callee. Send value out; callee sends some back.
    function spend(uint256 amount) external returns (uint256) {
        (bool ok,) = callee.call{value: amount}(
            abi.encodeWithSignature("takeAndRefund()")
        );
        require(ok, "callee");
        return address(this).balance;
    }

    // Lane 4: transient mutation. tk := 1, callee reenters bump() -> tk := 2.
    function bump() external {
        tk = tk + 1;
    }

    function transientRoundTrip() external returns (uint256) {
        tk = 1;
        (bool ok,) = callee.call(abi.encodeWithSignature("notifyBump()"));
        require(ok, "callee");
        return tk;
    }

    // Lane 5: create-with-reentry. Deploy a child whose constructor reenters
    // setX(7). Model side uses a create row + delta.
    function deploy() external returns (uint256) {
        new ReentrancyAdoptionChild(payable(address(this)));
        return x;
    }
}

contract ReentrancyAdoptionChild {
    constructor(address payable victim) {
        ReentrancyAdoptionVictim(victim).setX(7);
    }
}

/// Real reentering attacker for Forge ground truth.
contract ReentrancyAdoptionAttacker {
    ReentrancyAdoptionVictim public victim;

    function setVictim(address payable v) external {
        victim = ReentrancyAdoptionVictim(v);
    }

    function notify() external {
        victim.setX(42);
    }

    function notifyBump() external {
        victim.bump();
    }

    function takeAndRefund() external payable {
        // Send half of the received value back to the victim.
        (bool ok,) = address(victim).call{value: msg.value / 2}("");
        require(ok, "refund");
    }

    receive() external payable {}
}
