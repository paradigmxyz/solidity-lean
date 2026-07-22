// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.3 (X-RETABI retired, revert channel): a custom-error revert with
// NESTED-DYNAMIC params (uint256[][], string) is decoded by the recursive ABI
// codec into solidity-lean's rendering and COMPARED. Both engines must render
// revert|custom:Nested:[[w:1,w:2],[w:3]],b:0x7879.
contract NestedErr {
    error Nested(uint256[][] m, string s);

    function f() external pure {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](2);
        m[0][0] = 1;
        m[0][1] = 2;
        m[1] = new uint256[](1);
        m[1][0] = 3;
        revert Nested(m, "xy");
    }
}
