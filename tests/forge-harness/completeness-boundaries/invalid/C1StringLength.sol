// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// C1: `string` has no `.length` member (solc ArrayType::nativeMembers gates
// `length` on `!isString()`); the program must write `bytes(s).length`.
contract C1StringLength {
    function f(string memory s) public pure returns (uint256) {
        return s.length;
    }
}
