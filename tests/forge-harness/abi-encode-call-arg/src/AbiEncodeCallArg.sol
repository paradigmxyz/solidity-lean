// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// ABI-ENCODE-INTERNAL-CALL-ARG (#174): a direct internal call used as an argument
// to the `abi.encode`/`abi.encodePacked` builtin. solc accepts and lowers this
// (the internal call is evaluated, then its result is ABI-encoded), so on the
// real EVM `abi.encode(g())` returns the 32-byte encoding of uint256(3), and
// `abi.encode(uint256(9), g())` returns the two 32-byte words 9 and 3.
// solidity-lean's three `abi.*` member-call arms of the internal-call-aware
// statement lowering (return / var-decl / discard positions) fell through to the
// env-less `Stmt.toCore?` WITHOUT invoking the argument-position call hoister, so
// the nested internal call could not be lowered (TypeError.unsupported), poisoning
// the whole contract's executable lowering. The fix routes those three arms
// through the existing hoister (`Stmt.argPositionHoist?` /
// `Expr.argPositionHoistPrefix?`) before the env-less fallback, exactly as the
// ident-call / tuple-return / newExpr arms already do. The functions below return
// the RAW `abi.encode(...)` bytes (the exact divergence shape); the Forge test
// decodes them and the Lean witness pins the raw byte lists.
contract AbiEncodeCallArgTarget {
    function g() internal pure returns (uint256) { return 3; }

    // return position, single arg: abi.encode(g()) = 32-byte word 3.
    function encReturn() external pure returns (bytes memory) {
        return abi.encode(g());
    }

    // return position, two args (call is the SECOND arg):
    // abi.encode(uint256(9), g()) = word 9 followed by word 3.
    function encTwoArgs() external pure returns (bytes memory) {
        return abi.encode(uint256(9), g());
    }

    // wrapper: abi.encode(uint256(g()) + 1) = 32-byte word 4.
    function encWrapper() external pure returns (bytes memory) {
        return abi.encode(uint256(g()) + 1);
    }

    // var-decl position: bytes memory b = abi.encode(g()); = 32-byte word 3.
    function encVarDecl() external pure returns (bytes memory) {
        bytes memory b = abi.encode(g());
        return b;
    }

    // discard position: abi.encode(g()); as a bare expression statement, then
    // return 7 (proves the discard lowers and does not crash).
    function encDiscard() external pure returns (uint256) {
        abi.encode(g());
        return 7;
    }
}
