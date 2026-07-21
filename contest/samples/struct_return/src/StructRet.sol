// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.3 (X-RETABI retired): a STRUCT return with dynamic fields, a
// nested struct, and a static fixed array is decoded by the recursive ABI
// codec into solidity-lean's (..)/[..] rendering and COMPARED. Both engines
// must render success|(w:5,b:0x4142,[w:9],[w:1,w:2],(w:3)).
contract StructRet {
    struct Inner {
        uint64 v;
    }

    struct Pack {
        uint256 a;
        bytes b;
        uint256[] c;
        uint64[2] fx;
        Inner i;
    }

    function pack() external pure returns (Pack memory p) {
        p.a = 5;
        p.b = hex"4142";
        p.c = new uint256[](1);
        p.c[0] = 9;
        p.fx[0] = 1;
        p.fx[1] = 2;
        p.i.v = 3;
    }
}
