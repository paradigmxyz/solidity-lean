// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

/// Stage A probes: narrow (uint8) checked arithmetic in CONDITION positions
/// and as comparison operands. Each fn either Panics 0x11 (checked overflow)
/// or returns a value. a=200, b=100 passed in => a+b = 300 overflows uint8.
contract CondNarrowCleanupHarnessTarget {
    // (1) while condition, call-free narrow overflow
    function whileCond(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        while ((a + b) < 250) { k++; a++; }
        return k;
    }

    // (2) for condition
    function forCond(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        for (uint256 i = 0; (a + b) < 250; i++) { k++; a++; if (k > 5) break; }
        return k;
    }

    // (3) do..while condition
    function doWhileCond(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        do { k++; } while ((a + b) < 250 && k < 3);
        return k;
    }

    // (4) plain comparison in return
    function plainCmp(uint8 a, uint8 b) public pure returns (bool) {
        return (a + b) < 250;
    }

    // (5) if condition
    function ifCond(uint8 a, uint8 b) public pure returns (uint256) {
        if ((a + b) < 250) { return 1; }
        return 2;
    }

    // (6) require condition
    function requireCond(uint8 a, uint8 b) public pure returns (uint256) {
        require((a + b) < 250, "nope");
        return 1;
    }

    // (6b) assert condition
    function assertCond(uint8 a, uint8 b) public pure returns (uint256) {
        assert((a + b) < 250);
        return 1;
    }

    // (7) discard-expression statement (narrow add as a statement)
    function exprStmt(uint8 a, uint8 b) public pure returns (uint256) {
        a + b;
        return 7;
    }

    // (8) equality comparison operand
    function eqCmp(uint8 a, uint8 b) public pure returns (bool) {
        return (a + b) == 44;
    }

    // SAFE CONTROL: same shapes, no overflow (a=3,b=4)
    function whileCondSafe(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        while ((a + b) < 10 && k < 4) { k++; a++; }
        return k;
    }

    function plainCmpSafe(uint8 a, uint8 b) public pure returns (bool) {
        return (a + b) < 10;
    }

    // UNCHECKED CONTROL: must WRAP at uint8 width, no panic. a=200,b=100 -> 44 < 250 -> true
    function uncheckedCmp(uint8 a, uint8 b) public pure returns (bool) {
        unchecked { return (a + b) < 250; }
    }

    function uncheckedWhile(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        unchecked {
            while ((a + b) < 250 && k < 3) { k++; }
        }
        return k;
    }

    // TRUNCATING-CAST CONTROL: explicit cast stays truncating (no panic)
    function castCmp(uint256 w) public pure returns (bool) {
        return uint8(w) < 250; // w=300 -> 44 -> true
    }

    // int8 negative-narrow condition control
    function intWhileCond(int8 a, int8 b) public pure returns (uint256) {
        uint256 k = 0;
        while ((a + b) > -100) { k++; a--; if (k > 3) return k; }
        return k;
    }

    // (9) nested logical condition: overflow under && in if
    function ifAndCond(uint8 a, uint8 b) public pure returns (uint256) {
        if ((a + b) < 250 && a > 0) { return 1; }
        return 2;
    }

    // (10) negated comparison condition: overflow under ! in if
    function ifNotCond(uint8 a, uint8 b) public pure returns (uint256) {
        if (!((a + b) < 250)) { return 1; }
        return 2;
    }

    // (11) index key: narrow overflow as array index
    function idxKey(uint8 a, uint8 b) public pure returns (uint256) {
        uint256[300] memory arr;
        arr[44] = 9;
        return arr[a + b];
    }

    // (12) internal call argument: narrow overflow as arg
    function inner(uint8 x) internal pure returns (uint256) { return x; }
    function callArg(uint8 a, uint8 b) public pure returns (uint256) {
        return inner(a + b);
    }

    // (13) while condition with && (logical op wrapping the overflow)
    function whileAndCond(uint8 a, uint8 b) public pure returns (uint256) {
        uint256 k = 0;
        while ((a + b) < 250 && k < 3) { k++; }
        return k;
    }
}
