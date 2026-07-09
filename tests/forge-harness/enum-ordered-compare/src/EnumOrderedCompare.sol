// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EnumOrderedCompareHarnessTarget {
    enum State { Init, Running, Done }

    // `<`
    function ltTrue() external pure returns (bool) { return State.Init < State.Done; }   // true
    function ltFalse() external pure returns (bool) { return State.Done < State.Init; }   // false

    // `>`
    function gtTrue() external pure returns (bool) { return State.Done > State.Init; }    // true
    function gtFalse() external pure returns (bool) { return State.Init > State.Done; }   // false

    // `<=`
    function leTrueLt() external pure returns (bool) { return State.Init <= State.Done; }        // true (strict)
    function leTrueEq() external pure returns (bool) { return State.Running <= State.Running; }   // true (equal)
    function leFalse() external pure returns (bool) { return State.Done <= State.Init; }          // false

    // `>=`
    function geTrue() external pure returns (bool) { return State.Done >= State.Running; }   // true
    function geTrueEq() external pure returns (bool) { return State.Init >= State.Init; }     // true (equal)
    function geFalse() external pure returns (bool) { return State.Init >= State.Done; }      // false

    // `require(state < State.Done)` gate pattern over an enum parameter.
    function gate(State s) external pure returns (bool) { return s < State.Done; }
}
