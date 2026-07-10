// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Divergence lane: solc defers ALL element validation of a CALLDATA-location
// array/struct to ACCESS time. `abiDecodingFunctionCalldataArray` /
// `...Struct` (ABIFunctions.cpp) read NO value elements at the dispatch
// boundary -- only the length and the stride bound check -- and return a
// calldata pointer. A value element is validated only when it is ACCESSED
// (calldataAccessFunction -> abiDecodingFunctionValueType). So a DIRTY value
// element (e.g. a `bool` whose word is 2, an `address` with dirty high bits)
// that the function body never reads does NOT cause a revert; the same element
// DOES revert (empty `revert(0,0)`) the moment it is accessed.
//
// This contract exposes, for a `bool[]`, an `address[]`, and a fully-static
// calldata struct, both a "never-access-the-dirty-element" entry (returns only
// `.length` / a clean sibling) and an "access-the-dirty-element" entry. The
// Forge test drives each with hand-built calldata carrying a dirty element.
contract CalldataLazyValueHarnessTarget {
    // ----- bool[] calldata (element cleanup = none; eager-validated in model) -
    // Never touches the (dirty) element -> solc SUCCEEDS, returns length.
    function boolLen(bool[] calldata b) external pure returns (uint256) {
        return b.length;
    }

    // Accesses b[i] -> solc reverts empty on a dirty element.
    function boolAt(bool[] calldata b, uint256 i) external pure returns (bool) {
        return b[i];
    }

    // ----- address[] calldata (dirty high bits) -----------------------------
    function addrLen(address[] calldata a) external pure returns (uint256) {
        return a.length;
    }

    function addrAt(address[] calldata a, uint256 i)
        external
        pure
        returns (address)
    {
        return a[i];
    }

    // ----- fully-static calldata struct with a dirty value member -----------
    struct S {
        bool flag;   // may be dirty
        uint256 val; // clean sibling
    }

    // Reads only the clean sibling -> solc SUCCEEDS even if `flag` is dirty.
    function structVal(S calldata s) external pure returns (uint256) {
        return s.val;
    }

    // Reads the (dirty) `flag` member -> solc reverts empty.
    function structFlag(S calldata s) external pure returns (bool) {
        return s.flag;
    }
}
