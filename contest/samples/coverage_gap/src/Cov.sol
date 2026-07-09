// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// COVERAGE_GAP sample (SYNTHETIC - see claim.json). solc accepts + runs this
// and the Forge test passes; the sample exercises the lane-C classification for
// a solidity-lean fail-closed (importer 'unimplemented'). Because the live importer
// coverage gaps are being fixed on sibling branches, run_samples.py SIMULATES
// the solidity-lean fail-closed result for this sample (clearly marked) so the
// COVERAGE_GAP decision branch is exercised deterministically.
contract Cov {
    function run() external pure returns (uint256) {
        return 7;
    }
}
