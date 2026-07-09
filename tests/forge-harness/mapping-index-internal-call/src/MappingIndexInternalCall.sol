// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// MI1 — an INTERNAL function-call result used AS a mapping/array INDEX, in both
// the lvalue (`m[idu8(k)] = v`) and rvalue (`return m[idu8(k)]`) positions, for
// a uint256-valued mapping, a narrow (uint8) valued mapping, and a dynamic
// array. solc accepts these (ordinary Solidity); solidity-lean formerly
// over-rejected them at Executable lowering because the index operand of an
// index-access had no internal-call hoisting fallback (the same machinery
// constructor bodies / state-var initializers use). Evaluation order — solc
// evaluates the RHS before the LHS index — is pinned by runOrder(): with
// log == 0, the RHS `log + 100` is read before bump() sets log = 5, so the
// stored value is 100 (an index-first order would store 105).
contract MappingIndexInternalCallHarnessTarget {
    mapping(uint8 => uint256) m;
    mapping(uint8 => uint8) nm;   // narrow value: exercises read-side handling
    uint256[] arr;
    uint256 public log;

    function idu8(uint8 x) internal pure returns (uint8) { return x; }

    // Index call with a side effect, used by the evaluation-order probe.
    function bump() internal returns (uint8) { log = 5; return 0; }

    // Internal call in both the lvalue and rvalue index positions.
    function runMapping(uint8 k, uint256 v) external returns (uint256) {
        m[idu8(k)] = v;
        return m[idu8(k)];
    }

    function readMapping(uint8 k) external view returns (uint256) {
        return m[idu8(k)];
    }

    // Narrow (uint8) mapping value: the read result is width-narrow.
    function runNarrow(uint8 k, uint8 w) external returns (uint8) {
        nm[idu8(k)] = w;
        return nm[idu8(k)];
    }

    // Dynamic-array index in both positions.
    function runArray(uint8 i, uint256 v) external returns (uint256) {
        while (arr.length <= i) arr.push(0);
        arr[idu8(i)] = v;
        return arr[idu8(i)];
    }

    // Evaluation order probe: solc evaluates the RHS before the LHS index.
    // With log == 0 the RHS `log + 100` reads 0 BEFORE bump() sets log = 5,
    // so m[0] is stored as 100 (an index-first order would store 105).
    function runOrder() external returns (uint256) {
        log = 0;
        m[bump()] = log + 100;
        return m[0];
    }
}
