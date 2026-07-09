// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// `[0x11,0x22]` is uint8[2] (number literals), not bytes1[2]; ↛ bytes1[2].
contract BytesArrLiteral {
    function f() public pure {
        bytes1[2] memory x = [0x11, 0x22];
        x;
    }
}
