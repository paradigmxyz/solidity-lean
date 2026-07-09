// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Harness-hardening probe: revert() produces ZERO-length revert data (no Error,
// no Panic selector). Both engines must render revert|empty -- if solidity-lean
// emits revert|raw:0x (empty) or anything else while the EVM side renders
// revert|empty, that's the same raw-vs-decoded asymmetry class as round 21 and
// would fabricate a wrong-revert gap. entry g() covers the require(false) form.
contract Emptier {
    function f() external pure returns (uint256) {
        revert();
    }

    function g() external pure returns (uint256) {
        require(false);
        return 0;
    }
}
