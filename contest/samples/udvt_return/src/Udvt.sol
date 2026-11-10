// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: user-defined value types in the entry signature. The ABI
// encodes a UDVT as its underlying type, so the EVM-side decoder must read the
// file-level U (int128) and the contract-level V (int8) as SIGNED integers,
// including inside a fixed array and a struct member. Before the harness
// resolved UDVTs (measure._param_type), the return type was the bare name U
// and a negative value decoded as the unsigned word 2^256-7 (a fake gap).
type U is int128;
type W is uint16;

contract Udvt {
    type V is int8;

    struct S {
        U a;
        V b;
        W c;
    }

    enum E { A, B, C }

    function f(U p, V q) external pure returns (U, V[2] memory, S memory, E, W[] memory) {
        V[2] memory vs = [q, V.wrap(V.unwrap(q) + 1)];
        S memory s = S(U.wrap(U.unwrap(p) * 2), q, W.wrap(65535));
        W[] memory ws = new W[](2);
        ws[0] = W.wrap(1);
        ws[1] = W.wrap(2);
        return (p, vs, s, E.C, ws);
    }
}
