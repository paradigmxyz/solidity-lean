// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: a `string` return whose value contains the contest
// normal-form delimiters (`|`, `:`, and the `##EVT##` section token). If the
// engines rendered strings as raw text this would DESYNC the comparator; both
// must hex-encode it (`b:0x..`) so equal behavior stays equal. Also probes
// whether solidity-lean models a string return as Value.bytes (vs the `r:`
// reprStr fallback), which would fabricate a wrong-value gap.
contract StrReturn {
    function f() external pure returns (string memory) {
        return "a|b:c##EVT##d";
    }
}
