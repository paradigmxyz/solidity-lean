// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Accepted controls for the inline-array-literal widen boundary: every array
// literal here is assigned to a target whose element type EQUALS solc's
// bottom-up literal element type, so solc accepts it. Each function reads the
// stored elements back into a scalar so both Forge and the Lean interpreter can
// pin the runtime values.
contract ArrayLiteralWidenHarnessTarget {
    // uint8[3] = [1,2,3] (common mobile type uint8 == target). -> 1*10000+2*100+3
    function uint8Elems() external pure returns (uint256) {
        uint8[3] memory x = [1, 2, 3];
        return uint256(x[0]) * 10000 + uint256(x[1]) * 100 + uint256(x[2]);
    }

    // uint256[3] = [uint256(1),2,3] (explicit element forces uint256). -> 40506
    function explicit256Elems() external pure returns (uint256) {
        uint256[3] memory x = [uint256(1), 2, 3];
        return x[0] * 40000 + x[1] * 300 + x[2] * 2;
    }

    // int8[2] = [int8(-1),2] (common type int8; order-sensitive). Reading the
    // stored int8(-1) back through uint8 gives 255 (two's complement), so the
    // runtime value 255002 pins both x[0]=-1 and x[1]=2 as a positive word.
    function int8Elems() external pure returns (uint256) {
        int8[2] memory x = [int8(-1), 2];
        return uint256(uint8(x[0])) * 1000 + uint256(uint8(x[1]));
    }

    // uint8[2][2] = [[1,2],[3,4]] (nested common type uint8). -> 1234
    function multi8Elems() external pure returns (uint256) {
        uint8[2][2] memory x = [[1, 2], [3, 4]];
        return uint256(x[0][0]) * 1000 + uint256(x[0][1]) * 100
            + uint256(x[1][0]) * 10 + uint256(x[1][1]);
    }
}
