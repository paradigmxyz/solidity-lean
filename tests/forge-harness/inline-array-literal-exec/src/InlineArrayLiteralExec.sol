// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// AL-EXEC (task #58): executable shapes that USE an inline array literal in a
// function body. Every literal here is element-type-matched to its fixed-size
// memory-array target (so pinned solc 0.8.35 accepts and runs it), and each
// function reads the stored elements back into a scalar so both Forge (EVM) and
// the solidity-lean interpreter (ownCall) pin the SAME runtime value. Before the
// AL-EXEC fix the interpreter over-rejected the undecorated narrow-int literals
// (`uint8[3] = [1,2,3]`, `uint8[2][2] = [[1,2],[3,4]]`) at executable lowering.
contract InlineArrayLiteralExecTarget {
    // var-init, bare (undecorated) narrow-int literals -> uint8[3]. 1*10000+2*100+3
    function varInitNarrow() external pure returns (uint256) {
        uint8[3] memory a = [1, 2, 3];
        return uint256(a[0]) * 10000 + uint256(a[1]) * 100 + uint256(a[2]);
    }

    // var-init, bare nested narrow-int literals -> uint8[2][2]. -> 1234
    function multidimNarrow() external pure returns (uint256) {
        uint8[2][2] memory m = [[1, 2], [3, 4]];
        return uint256(m[0][0]) * 1000 + uint256(m[0][1]) * 100
            + uint256(m[1][0]) * 10 + uint256(m[1][1]);
    }

    // element read of a literal directly (index-of-literal). i=1 -> 20
    function indexOfLiteral(uint256 i) external pure returns (uint256) {
        return [uint256(10), 20, 30][i];
    }

    // pass an inline literal as an argument to an internal function. -> 18
    function sum3(uint256[3] memory a) internal pure returns (uint256) {
        return a[0] + a[1] + a[2];
    }
    function argToInternal() external pure returns (uint256) {
        return sum3([uint256(5), 6, 7]);
    }

    // return an inline literal directly (fresh fixed memory array). [1,2,3]
    function returnLiteral() external pure returns (uint256[3] memory) {
        return [uint256(1), 2, 3];
    }

    // int8 narrow literal with a negative leading element (order-sensitive);
    // read back through uint8 (two's complement) so the value stays positive.
    // uint8(-1)=255 -> 255*1000 + 2 = 255002
    function int8Narrow() external pure returns (uint256) {
        int8[2] memory x = [int8(-1), 2];
        return uint256(uint8(x[0])) * 1000 + uint256(uint8(x[1]));
    }
}
