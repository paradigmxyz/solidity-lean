// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryArrayElement {
    function bad(L[] memory values) internal pure returns (uint256) {
        return values.length;
    }
}
