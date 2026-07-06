// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BadFixedPointStateInit {
    fixed128x18 private value = 1.25;
}
