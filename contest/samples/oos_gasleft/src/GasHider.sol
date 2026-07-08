// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// OUT_OF_SCOPE sample: the entry function looks benign, but a transitive callee
// reads gasleft() and returns it as the observable. The reject gate's
// WHOLE-SUBMISSION scan (design §2) must catch the hidden gasleft() in the
// callee (X-GASLEFT syntactic + SEM-GAS taint), even though the entry itself
// does not mention gas.
contract GasHider {
    function entry() external view returns (uint256) {
        return helper();
    }

    function helper() internal view returns (uint256) {
        // gas-as-observable, buried one call deep.
        return gasleft();
    }
}
