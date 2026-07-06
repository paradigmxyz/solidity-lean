// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryUsingTarget {
    using L for L;
}
