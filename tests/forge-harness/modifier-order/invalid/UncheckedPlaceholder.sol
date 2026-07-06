// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract UncheckedPlaceholder {
    modifier m() {
        unchecked {
            _;
        }
    }

    function bad() external m {}
}
