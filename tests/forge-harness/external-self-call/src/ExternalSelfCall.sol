// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// #186 EXTERNAL-SELF-CALL: a call to `address(this)` (`this.f()` /
// `address(this).call(...)`) is closed-world — it must self-dispatch through the
// contract's own code, not an open-world responder. Ground truth is real solc
// 0.8.35 + EVM.
contract ExternalSelfCallTarget {
    uint256 public x = 5;
    uint256 public counter;

    function getX() external view returns (uint256) { return x; }
    function inc() external returns (uint256) { counter += 1; return counter; }
    function whoami() external view returns (bool) { return msg.sender == address(this); }
    function boom() external pure returns (uint256) { revert("nope"); }

    // Value read through a self-call.
    function h() public returns (uint256) { return this.getX(); }
    // State mutation through a self-call persists.
    function doInc() public returns (uint256) { return this.inc(); }
    // msg.sender inside the self-called fn is address(this).
    function senderCheck() public returns (bool) { return this.whoami(); }
    // A reverting self-call routes to catch.
    function tryCatchBoom() public returns (uint256) {
        try this.boom() returns (uint256 v) { return v; }
        catch { return 42; }
    }
    // A low-level self-call to a reverting fn yields success = false.
    function lowLevelBoom() public returns (bool) {
        (bool ok, ) = address(this).call(abi.encodeWithSignature("boom()"));
        return ok;
    }
}

// `this.f()` in a CONSTRUCTOR reverts (extcodesize(this) == 0), so deploy reverts.
contract ExternalSelfCallCtor {
    uint256 public y;
    function getY() external view returns (uint256) { return y; }
    constructor() { y = this.getY(); }
}
