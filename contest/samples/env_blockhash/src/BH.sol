// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// UNPINNABLE-ENV ATTACK (review E-1 / SEM-ENV). Entry returns blockhash(0),
// which solidity-lean has no faithful model for (no historical block hashes). The
// env-fact detector must classify this OUT_OF_SCOPE, not let it be a spurious
// SOUNDNESS_GAP.
contract BH {
    function bh() external view returns (bytes32) { return blockhash(0); }
}
