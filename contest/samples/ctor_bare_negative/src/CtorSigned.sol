// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Guard check: a BARE negative constructor arg (-5, not {"int":-5}) must be
// REJECT_MALFORMED via the SAME _arg_domain_error path as entry args (round 16),
// not slip through to a Lean render crash. Confirms ctor-arg domain validation
// parity with entry-arg validation.
contract CtorSigned {
    int8 private x;

    constructor(int8 a) {
        x = a;
    }

    function f() external view returns (int8) {
        return x;
    }
}
