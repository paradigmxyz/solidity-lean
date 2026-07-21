// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// ITEM-5 (operator using-for resolution): shapes whose OPERANDS the strict
// operand-shape gate (`usingFreeFunctionOperands?`) may fail to type, so the
// operator rewrite silently declined and the whole function over-rejected.
// The sound fallback binds the unique free function whose parameters all
// equal the using-directive's target UDVT — solc's own binding rule.
type Pt is uint128;

function ptAdd(Pt a, Pt b) pure returns (Pt) {
    return Pt.wrap(Pt.unwrap(a) + Pt.unwrap(b));
}

function ptSub(Pt a, Pt b) pure returns (Pt) {
    return Pt.wrap(Pt.unwrap(a) - Pt.unwrap(b));
}

function ptNeg(Pt a) pure returns (Pt) {
    return Pt.wrap(0) - a;
}

function ptEq(Pt a, Pt b) pure returns (bool) {
    return Pt.unwrap(a) == Pt.unwrap(b);
}

using {ptAdd as +, ptSub as -, ptNeg as -, ptEq as ==} for Pt global;

contract OperatorUdvtResolutionHarnessTarget {
    Pt stored;

    // Baseline: single operator application on wrapped params.
    function opAdd(uint128 a, uint128 b) external pure returns (uint128) {
        return Pt.unwrap(Pt.wrap(a) + Pt.wrap(b));
    }

    // Chained operators: the second `+`'s left operand is the REWRITTEN
    // call `ptAdd(a, b)`.
    function opChain(uint128 a, uint128 b, uint128 c)
        external pure returns (uint128)
    {
        return Pt.unwrap(Pt.wrap(a) + Pt.wrap(b) + Pt.wrap(c));
    }

    // Mixed binary/unary chain: `-(x + y)` then `- z`.
    function opMixed(uint128 a, uint128 b, uint128 c)
        external pure returns (uint128)
    {
        Pt x = Pt.wrap(a);
        Pt y = Pt.wrap(b);
        Pt z = Pt.wrap(c);
        return Pt.unwrap(-(x + y) - z);
    }

    // Operand from a STORAGE state variable.
    function opStorage(uint128 a) external returns (uint128) {
        stored = Pt.wrap(a);
        return Pt.unwrap(stored + Pt.wrap(1));
    }

    // Operand is a ternary over UDVT locals.
    function opTernary(uint128 a, uint128 b, bool c)
        external pure returns (uint128)
    {
        Pt x = Pt.wrap(a);
        Pt y = Pt.wrap(b);
        return Pt.unwrap((c ? x : y) + Pt.wrap(2));
    }

    // Comparison operator via using-for; operand is a rewritten `+` call.
    function opEqChain(uint128 a, uint128 b) external pure returns (bool) {
        return (Pt.wrap(a) + Pt.wrap(b)) == Pt.wrap(a + b);
    }

    // Operand is an internal function call returning the UDVT.
    function mk(uint128 v) internal pure returns (Pt) {
        return Pt.wrap(v);
    }

    function opCallOperand(uint128 a, uint128 b)
        external pure returns (uint128)
    {
        return Pt.unwrap(mk(a) + mk(b));
    }
}
