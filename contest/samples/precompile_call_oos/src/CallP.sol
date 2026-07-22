// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// X-EXTCALL (register 1.6): the precompile carve-out covers ONLY plain
// `.staticcall` with a literal 1..10 receiver. A value-free low-level `.call`
// to the same precompile address is NOT answered in-semantics (engine probe:
// only a zero-value STATICCALL request reaches precompileAnswerCall?), so it
// stays out of scope.
contract CallP {
    function run(uint256 x) external returns (bool) {
        (bool ok, ) = address(2).call(abi.encode(x));
        return ok;
    }
}
