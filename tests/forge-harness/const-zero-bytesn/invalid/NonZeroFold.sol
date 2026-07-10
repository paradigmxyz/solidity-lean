// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Over-accept guard: `1 + 1` folds to 2, which is NOT implicitly convertible to
// bytesN. solc rejects; the model must too.
contract NonZeroFold {
    function f() external pure returns (bytes32) {
        bytes32 x = 1 + 1;
        return x;
    }
}
