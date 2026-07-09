// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// CMP-MIXEDSIGN #86 accept controls: same-sign folded integer-literal
// comparisons still fold and are accepted by solc AND solidity-lean.

contract C {
    function bothPos() public pure returns (bool) { return 1 < 2; }
    function bothNeg() public pure returns (bool) { return (0 - 1) < (0 - 2); }
}
