// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// Sibling-expression evaluation order probes (R1: intrinsic per-construct
/// order). Every function resets the counter and exposes the order through
/// `i++` side effects, so the returned values / event payloads pin the order.
contract EvalOrderIntrinsic {
    uint256 public i;
    uint256 public s;
    mapping(uint256 => mapping(uint256 => uint256)) public m;

    event Mixed(uint256 indexed a, uint256 b, uint256 indexed c, uint256 d);
    event AllData(uint256 a, uint256 b, uint256 c);
    error Err(uint256 a, uint256 b);

    // --- LEFT-to-RIGHT constructs ---

    /// Tuple RHS: `(a, b) = (i++, i)` -> (0, 1).
    function tupleRhs() public returns (uint256, uint256) {
        i = 0;
        uint256 a;
        uint256 b;
        (a, b) = (i++, i);
        return (a, b);
    }

    /// Return tuple: `return (i++, i++)` -> (0, 1).
    function returnTuple() public returns (uint256, uint256) {
        i = 0;
        return (i++, i++);
    }

    /// Internal-call arguments left-to-right: sink(i++, i++, i++) -> 012.
    function callArgs() public returns (uint256) {
        i = 0;
        return sink(i++, i++, i++);
    }

    function sink(uint256 a, uint256 b, uint256 c)
        internal
        pure
        returns (uint256)
    {
        return a * 100 + b * 10 + c;
    }

    /// abi.encode args left-to-right: abi.encode(i++, i++) encodes (0, 1).
    function abiEnc() public returns (bytes memory) {
        i = 0;
        return abi.encode(i++, i++);
    }

    /// Index lvalue base-then-key: `m[i++][i++] = 99` writes m[0][1].
    function indexLhs() public returns (uint256) {
        i = 0;
        m[i++][i++] = 99;
        return m[0][1];
    }

    /// Custom-error args left-to-right: revert Err(i++, i++) -> Err(0, 1).
    function revertErr() public {
        i = 0;
        revert Err(i++, i++);
    }

    // --- emit: two-phase (indexed reverse, then data forward) ---

    /// All-data event: data args evaluate left-to-right -> (0, 1, 2).
    function emitAllData() public {
        i = 0;
        emit AllData(i++, i++, i++);
    }

    /// Mixed event `Mixed(indexed a, b, indexed c, d)`: the INDEXED args are
    /// evaluated in REVERSE source order first (c then a), then the data args
    /// forward (b then d): c=0, a=1, b=2, d=3.
    function emitMixed() public {
        i = 0;
        emit Mixed(i++, i++, i++, i++);
    }

    // --- PRESERVED right-to-left / RHS-first controls ---

    function wr() internal returns (uint256) {
        s = 5;
        return 0;
    }

    function rd() internal view returns (uint256) {
        return s;
    }

    /// Binary operands RIGHT then LEFT: rd() + wr() -> wr first (s=5, 0),
    /// then rd() reads 5 -> 5.
    function binaryOrder() public returns (uint256) {
        s = 0;
        return rd() + wr();
    }

    /// Assignment RHS before LHS-ref: `arr[i++] = i++` with i=0 evaluates the
    /// RHS first (0, i=1), then the index (1, i=2): arr = [7, 0, 7], i = 2.
    function arrAssign()
        public
        returns (uint256, uint256, uint256, uint256)
    {
        i = 0;
        uint256[3] memory arr = [uint256(7), 7, 7];
        arr[i++] = i++;
        return (arr[0], arr[1], arr[2], i);
    }

    /// Compound assign RHS before LHS-ref: `arr[i++] += i++` with i=0 adds the
    /// RHS (0) into arr[1]: arr = [7, 7, 7], i = 2.
    function arrCompound()
        public
        returns (uint256, uint256, uint256, uint256)
    {
        i = 0;
        uint256[3] memory arr = [uint256(7), 7, 7];
        arr[i++] += i++;
        return (arr[0], arr[1], arr[2], i);
    }

    /// Short-circuit stays left-first with a guarded right operand.
    function scAnd() public returns (uint256) {
        i = 0;
        bool r = (i++ == 100) && (i++ == 0);
        return r ? 1000 + i : i; // right side never runs: i == 1
    }

    function scOr() public returns (uint256) {
        i = 0;
        bool r = (i++ == 0) || (i++ == 100);
        return r ? 1000 + i : i; // right side never runs: i == 1 -> 1001
    }

    /// Data-dependent sibling pair: one sibling reads what the other writes.
    function dataDep() public returns (uint256, uint256) {
        i = 0;
        (uint256 a, uint256 b) = (i = 5, i + 1);
        return (a, b); // left-to-right: (5, 6)
    }
}

/// Inline array literal with side-effecting components (kept in a separate
/// contract: the Lean importer does not yet lower non-literal inline-array
/// components, so this construct is pinned by the Forge lane only; the model
/// evaluates `Expr.fixedArray` components through the same left-to-right list
/// evaluator pinned by the tuple/argument probes above).
contract EvalOrderInlineArray {
    uint256 public i;

    /// Inline array literal left-to-right: [i++, i++, i++] -> [0, 1, 2].
    function inlineArray() public returns (uint256, uint256, uint256) {
        i = 0;
        uint256[3] memory arr = [i++, i++, i++];
        return (arr[0], arr[1], arr[2]);
    }
}
