// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract RequireUintReason {
    function badRequireUintReason() external pure {
        require(true, 7);
    }
}
