// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract FpNeg { function f(fixed128x18 a) external pure returns (fixed128x18) { fixed128x18 b = -a; return b; } }
