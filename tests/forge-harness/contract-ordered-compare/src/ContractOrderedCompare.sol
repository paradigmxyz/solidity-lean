// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 accepts ordered comparison (`<`/`<=`/`>`/`>=`) of two contract-
// or interface-typed operands, comparing their addresses as unsigned 160-bit
// values (only emits deprecation warning 9170; still compiles). Contract-typed
// parameters are ABI-decoded from calldata as the operand's address word, so the
// Lean runtime witnesses below seed deterministic addresses.

// The runtime-witness target compares operands of its OWN contract type (and
// `this`), so the single-contract witness context resolves every operand.
contract ContractOrderedCompareHarnessTarget {
    function lt(ContractOrderedCompareHarnessTarget a, ContractOrderedCompareHarnessTarget b)
        external pure returns (bool) { return a < b; }
    function gt(ContractOrderedCompareHarnessTarget a, ContractOrderedCompareHarnessTarget b)
        external pure returns (bool) { return a > b; }
    function le(ContractOrderedCompareHarnessTarget a, ContractOrderedCompareHarnessTarget b)
        external pure returns (bool) { return a <= b; }
    function ge(ContractOrderedCompareHarnessTarget a, ContractOrderedCompareHarnessTarget b)
        external pure returns (bool) { return a >= b; }

    // Self-compare: irreflexive `<` is false, reflexive `<=` is true.
    function ltSelf(ContractOrderedCompareHarnessTarget a) external pure returns (bool) { return a < a; }
    function leSelf(ContractOrderedCompareHarnessTarget a) external pure returns (bool) { return a <= a; }

    // `this` is of the contract's own type; comparing it to itself is deterministic.
    function ltThis() external view returns (bool) { return this < this; }   // false
    function leThis() external view returns (bool) { return this <= this; }  // true
}

// Interface-typed operands are also contract types and compare as addresses.
interface CmpIface {}

contract InterfaceOrderedCompare {
    function ltIface(CmpIface a, CmpIface b) external pure returns (bool) { return a < b; }
}

// Base/derived operands upcast to the common base and compare as addresses
// (solc resolves the common contract type; unrelated contracts have none).
contract CmpBase {}
contract CmpDerived is CmpBase {}

contract BaseDerivedOrderedCompare {
    function ltBaseDerived(CmpBase a, CmpDerived b) external pure returns (bool) { return a < b; }
}
