// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// #126 ARRAY-WIDEN-COPY — copy assignment INTO a FIXED storage array whose
// element type is a NON-integer value type (`bytes32`), from a shorter fixed
// memory source. solc accepts these (ArrayType::isImplicitlyConvertibleTo,
// Types.cpp:1640-1648): a fixed dest `T[N]` accepts a fixed source `S[M]` with
// N >= M when the base is implicitly convertible; the first M elements are
// copied and the old tail (indices M..N-1) is zero-cleared. solidity-lean
// formerly over-rejected every non-integer element type (the base gate was
// `isInteger`). The legacy struct-value carve-out is unaffected (the element
// here is a value type, not a struct).
contract ArrayWidenCopyHarnessTarget {
    bytes32[3] a;

    // bytes32[2] memory -> bytes32[3] storage: first two elements copied, the
    // pre-set tail (index 2) is cleared to zero.
    function copyWidenClearsTail(bytes32 x, bytes32 y)
        external
        returns (bytes32, bytes32, bytes32)
    {
        a[0] = bytes32(uint256(0xdead));
        a[1] = bytes32(uint256(0xbeef));
        a[2] = bytes32(uint256(0xcafe)); // pre-set tail nonzero
        bytes32[2] memory m;
        m[0] = x;
        m[1] = y;
        a = m;                            // widen-copy
        return (a[0], a[1], a[2]);        // expect (x, y, 0)
    }
}
