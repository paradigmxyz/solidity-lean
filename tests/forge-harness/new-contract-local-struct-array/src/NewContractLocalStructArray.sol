// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #163 NEW-CONTRACT-LOCAL-STRUCT-ARRAY — over-reject. solc 0.8.35 accepts and
// executes `new P[](n)` where `P` is a CONTRACT-LOCAL struct. The model's checker
// rejected it: the `Ty.array _ none` branch of the `new`-array type-check
// returned the RAW AST element type `["P"]`, but every TARGET type (declared
// locals, returns, params) qualifies a contract-local struct ref to
// `["C","P"]` via `Ty.qualifyLocalUserTypes`. The unqualified `["P"]` then never
// matched the qualified target, so `expectAssignableTo` failed
// (TypeError.expectedType (array ["C","P"]) (array ["P"])). The fix runs the
// `new`-array RESULT element type through the same current-scope qualification
// (`CheckEnv.qualifyCurrentLocalUserTypes`), which only qualifies to a path that
// is actually known in the enclosing scope, so elementary-element and
// file-level-struct arrays are untouched.
//
// Isolation ladder pinned in one contract: local-var of a local-struct array
// (G, the fix), a return of a local-struct array (G2), a MULTI-field local
// struct (G3), an array-of-array of the local struct (G4), and an elementary
// element array (H, must stay working).
contract NewContractLocalStructArrayHarness {
    struct P { uint256 x; }
    struct Q { uint256 x; address y; bool z; }

    // G: local var of a contract-local struct array — the over-reject the fix closes.
    function localVarLen() external pure returns (uint256) {
        P[] memory pa = new P[](3);
        return pa.length;
    }

    // G2: return-position of a contract-local struct array (the exact repro shape).
    function returnArr() external pure returns (P[] memory) {
        return new P[](1);
    }

    // G3: MULTI-field contract-local struct array.
    function multiLen() external pure returns (uint256) {
        Q[] memory qa = new Q[](2);
        return qa.length;
    }

    // G4: array-of-array of the contract-local struct.
    function arr2Len() external pure returns (uint256) {
        P[][] memory aa = new P[][](4);
        return aa.length;
    }

    // H: elementary element array (already worked; pinned for the ladder).
    function uintLen() external pure returns (uint256) {
        uint256[] memory ua = new uint256[](5);
        return ua.length;
    }
}
