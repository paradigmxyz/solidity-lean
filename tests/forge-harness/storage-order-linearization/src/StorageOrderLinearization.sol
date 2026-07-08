// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// DL1 regression: storage slot layout and base-constructor / inline-initializer
// execution order must both follow reverse(C3 linearization) = most-base-first,
// exactly as solc lays out storage (Types.cpp reverse(linearizedBaseContracts))
// and runs constructors.  The naive left-to-right DFS post-order this replaced
// diverged whenever a contract lists a direct base that is ALSO an indirect base
// (the `Dl1Sh*` shape below).
//
// Every contract shares the `Dl1Root` base, which carries an order-sensitive
// `trace` accumulator: each constructor appends its id via `_log`, so the final
// `trace` value encodes the exact constructor execution order.  `trace` sits at
// slot 0 of every derived contract, and each contract's own `uint256` lands in
// the next slots in most-base-first order, so raw-slot reads pin the layout.

contract Dl1Root {
    uint256 public trace;
    function _log(uint256 id) internal { trace = trace * 10 + id; }
}

// Linear control: A <- B <- C. DFS and reverse-C3 coincide here.
contract Dl1LinA is Dl1Root { uint256 public a; constructor() { a = 11; _log(1); } }
contract Dl1LinB is Dl1LinA { uint256 public b; constructor() { b = 22; _log(2); } }
contract Dl1LinC is Dl1LinB { uint256 public c; constructor() { c = 33; _log(3); } }

// Simple diamond control: D; E,F is D; G is E,F. DFS and reverse-C3 coincide.
contract Dl1DiaD is Dl1Root { uint256 public d; constructor() { d = 44; _log(4); } }
contract Dl1DiaE is Dl1DiaD { uint256 public e; constructor() { e = 55; _log(5); } }
contract Dl1DiaF is Dl1DiaD { uint256 public f; constructor() { f = 66; _log(6); } }
contract Dl1DiaG is Dl1DiaE, Dl1DiaF { uint256 public g; constructor() { g = 77; _log(7); } }

// DL1 shared direct+indirect base: X,Y is Root; M is X,Y; Z is Y,M.
// `Z` lists `Y` as a direct base while `M` (also direct) lists `Y` indirectly.
// C3(Z) = [Z, M, Y, X, Root]; reverse = [Root, X, Y, M, Z].
// solc: sx@1, sy@2 and constructor order X,Y,M,Z (trace 1234).
// Buggy DFS gave sy@1, sx@2 (swapped) and order Y,X,M,Z (trace 2134).
contract Dl1ShX is Dl1Root { uint256 public sx; constructor() { sx = 111; _log(1); } }
contract Dl1ShY is Dl1Root { uint256 public sy; constructor() { sy = 222; _log(2); } }
contract Dl1ShM is Dl1ShX, Dl1ShY { uint256 public sm; constructor() { sm = 333; _log(3); } }
contract Dl1ShZ is Dl1ShY, Dl1ShM { uint256 public sz; constructor() { sz = 444; _log(4); } }
