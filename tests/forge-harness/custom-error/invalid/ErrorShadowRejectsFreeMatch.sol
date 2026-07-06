// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

error Bad(uint256 value);

contract ErrorShadowRejectsFreeMatch {
    error Bad(address target);

    function fail() external pure {
        revert Bad(1);
    }
}
