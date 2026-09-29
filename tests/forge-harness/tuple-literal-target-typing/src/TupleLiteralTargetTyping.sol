// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

contract TupleLiteralTargetTyping {
    function hexDeclaration() external pure returns (bytes4, uint256) {
        (bytes4 value, uint256 other) = (hex"11223344", uint256(1));
        return (value, other);
    }

    function stringDeclaration() external pure returns (bytes4, uint256) {
        (bytes4 value, uint256 other) = ("abcd", uint256(2));
        return (value, other);
    }

    function hexAssignment() external pure returns (bytes4, uint256) {
        bytes4 value;
        uint256 other;
        (value, other) = (hex"11223344", uint256(3));
        return (value, other);
    }
}
