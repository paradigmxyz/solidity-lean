// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.4: a STRUCT ENTRY PARAMETER with DYNAMIC members (bytes +
// uint256[]) — the struct itself becomes an offset+tail encoding. The claim
// arg [9, {"bytes": "0xdeadbeef"}, [4, 5]] mirrors the member order.
contract StructDynArg {
    struct D {
        uint256 a;
        bytes data;
        uint256[] xs;
    }

    function probe(D memory d) external pure returns (uint256, bytes memory) {
        return (d.a + d.xs[0] + d.data.length, d.data);
    }
}
