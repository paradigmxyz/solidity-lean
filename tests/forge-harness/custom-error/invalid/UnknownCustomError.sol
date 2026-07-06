// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract UnknownCustomError {
    function bad() external pure {
        revert Missing(1);
    }
}
