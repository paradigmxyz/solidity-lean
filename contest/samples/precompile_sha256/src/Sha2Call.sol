// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.6 (X-EXTCALL precompile carve-out): a `.staticcall` whose
// receiver is a literal precompile address (here 0x2, sha256) is answered
// in-semantics by the engine with the REAL precompile output, so it is
// measured, not excluded.
contract Sha2Call {
    function digest(uint256 x) external view returns (bool, bytes32) {
        (bool ok, bytes memory out) = address(2).staticcall(abi.encode(x));
        return (ok, abi.decode(out, (bytes32)));
    }
}
