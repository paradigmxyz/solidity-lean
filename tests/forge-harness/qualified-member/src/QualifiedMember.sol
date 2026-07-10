// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// QUALIFIED-MEMBER — reading a member THROUGH a type-name qualifier
// (contract / interface / library) rather than through a value. solc accepts
// all of these; solidity-lean formerly over-rejected the whole contract because
// the type-name member arm could not lower a qualified CONSTANT, a qualified
// STATE VARIABLE, a nested qualified ENUM VALUE, or a qualified SELECTOR, and a
// library-qualified error in a `revert`.
interface I {
    error IE(uint256 x);
}

library L {
    uint256 constant LK = 42;
    function g(uint256 a) external pure returns (uint256) { return a + 1; }
    error LE(uint256 y);
}

contract Base {
    uint256 constant K = 7;
    enum E { A, B, C }
    uint256 v;
}

contract QualifiedMemberHarnessTarget is Base {
    // 1. qualified CONSTANT of a base contract and of a library
    function qualConstBase() external pure returns (uint256) { return Base.K; }
    function qualConstLib() external pure returns (uint256) { return L.LK; }

    // 2. qualified ENUM VALUE (nested member: contract -> enum type -> value)
    function qualEnum() external pure returns (uint256) { return uint256(Base.E.C); }

    // 3. qualified STATE VARIABLE of a base contract (inherited storage slot)
    function qualStateVar() external returns (uint256) {
        v = 8;
        return Base.v;          // resolves to the same inherited slot -> 8
    }

    // 4. qualified SELECTORs: interface error, library ext-fn, library error
    function ifaceErrSel() external pure returns (bytes4) { return I.IE.selector; }
    function libFnSel() external pure returns (bytes4) { return L.g.selector; }
    function libErrSel() external pure returns (bytes4) { return L.LE.selector; }

    // 5. library-qualified error in a revert
    function doRevert() external pure { revert L.LE(9); }
}
