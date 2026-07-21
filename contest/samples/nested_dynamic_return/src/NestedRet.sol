// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.3 (X-RETABI retired): nested-dynamic RETURN types are decoded by
// the recursive ABI codec into solidity-lean's [..] rendering and COMPARED.
// vals() returns (uint256[][], bytes[]) = ([[1,2],[3]], [0xaa, 0xbbcc]);
// both engines must render success|[[w:1,w:2],[w:3]],[b:0xaa,b:0xbbcc].
contract NestedRet {
    function vals() external pure
        returns (uint256[][] memory, bytes[] memory)
    {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](2);
        m[0][0] = 1;
        m[0][1] = 2;
        m[1] = new uint256[](1);
        m[1][0] = 3;
        bytes[] memory b = new bytes[](2);
        b[0] = hex"aa";
        b[1] = hex"bbcc";
        return (m, b);
    }
}
