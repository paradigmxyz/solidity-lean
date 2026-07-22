// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.4: a STRUCT ENTRY PARAMETER with static members. The JSON-list
// claim arg [40, 2] carries one element per member in declaration order,
// encoded inline (static tuple) on the EVM side, Value.tuple on the Lean side.
contract StructArg {
    struct P {
        uint256 a;
        uint64 b;
    }

    function join(P memory p) external pure returns (uint256) {
        return p.a + p.b;
    }
}
