// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract RevertUintReason {
    function badRevertUintReason() external pure {
        revert(7);
    }
}
