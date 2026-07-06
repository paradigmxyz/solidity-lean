// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventSameSignature {
    event Seen(uint256 first);
    event Seen(uint256 second);
}
