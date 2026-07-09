// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// `[[1,2],[3,4]]` is uint8[2][2]; ↛ uint256[2][2].
contract AssignWidenMultidim {
    function f() public pure {
        uint256[2][2] memory x = [[1, 2], [3, 4]];
        x;
    }
}
