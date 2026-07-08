// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {PackedNestedStaticArray} from "../src/PackedNestedStaticArray.sol";

contract PackedNestedStaticArrayForgeTest {
    PackedNestedStaticArray private target = new PackedNestedStaticArray();

    function requireBytesEq(
        bytes memory actual,
        bytes memory expected,
        string memory label
    ) internal pure {
        require(keccak256(actual) == keccak256(expected), label);
    }

    // Ground-truth packed layout: each innermost uint8 padded to a full 32-byte
    // word, elements in-place. matrix = [[1,2],[3,4]] -> word(1..4).
    function testPackedNestedStaticArray() public view {
        uint8[2][2] memory matrix;
        matrix[0][0] = 1;
        matrix[0][1] = 2;
        matrix[1][0] = 3;
        matrix[1][1] = 4;

        // Cross-check the contract output against solc's own abi.encodePacked
        // and pin the layout via its length (2*2 elements padded to 32 bytes).
        requireBytesEq(
            target.packMatrix(matrix),
            abi.encodePacked(matrix),
            "packed nested static array vs solc"
        );
        require(
            target.packMatrix(matrix).length == 128,
            "packed nested static array length"
        );
    }

    function testPackedDynamicOuter() public view {
        uint8[2][] memory rows = new uint8[2][](2);
        rows[0][0] = 9;
        rows[0][1] = 8;
        rows[1][0] = 7;
        rows[1][1] = 6;

        requireBytesEq(
            target.packDynamicOuter(rows),
            abi.encodePacked(rows),
            "packed dynamic-outer static-inner vs solc"
        );
        require(
            target.packDynamicOuter(rows).length == 128,
            "packed dynamic-outer length"
        );
    }
}
