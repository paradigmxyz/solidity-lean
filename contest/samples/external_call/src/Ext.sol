// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract Ext {
    // Makes an external LOW-LEVEL call. External calls are unmodeled in the v1
    // responder-free path (solidity-lean defaults them to fail/empty), so this is
    // X-EXTCALL out-of-scope. On real EVM a low-level call to a codeless address
    // succeeds with empty returndata -> returns true.
    function probe(address a) external returns (bool) {
        (bool ok, ) = a.call("");
        return ok;
    }
}
