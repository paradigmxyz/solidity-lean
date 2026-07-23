// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Storage state var; the typed leading element pins the literal type to
// uint16[2], which is NOT implicitly convertible to the narrower uint8[2]
// target (narrowing) even for a storage copy. solc REJECTS.
contract StateNarrow {
    uint8[2] arr = [uint16(1), 2];
}
