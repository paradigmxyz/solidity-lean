// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventIndexedOnly {
    event Seen(uint256 indexed value);
    event Seen(uint256 value);
}
