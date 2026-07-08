// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/MemoryAliasFixes.sol";

contract MemoryAliasFixesForgeTest {
    function checkPair(
        uint256 actualX,
        uint256 actualY,
        uint256 expectedX,
        uint256 expectedY
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
    }

    function testMemoryRefRhsAliases() public {
        MemoryAliasFixes t = new MemoryAliasFixes();
        (uint256 a, uint256 b) = t.ternaryDeclAlias(true);
        checkPair(a, b, 42, 42);
        (a, b) = t.ternaryAssignAlias(true);
        checkPair(a, b, 42, 42);
        (a, b) = t.indexAssignAlias();
        checkPair(a, b, 55, 55);
        (a, b) = t.memberAssignAlias();
        checkPair(a, b, 88, 88);
    }

    function testTupleDestructuringAliases() public {
        MemoryAliasFixes t = new MemoryAliasFixes();
        (uint256 a, uint256 b) = t.tupleAlias();
        checkPair(a, b, 7, 9);
        (a, b) = t.tupleSwap();
        checkPair(a, b, 1, 99);
        (a, b) = t.tupleDecl();
        checkPair(a, b, 44, 9);
    }

    function testStoreRefIntoAggregateAliases() public {
        MemoryAliasFixes t = new MemoryAliasFixes();
        (uint256 a, uint256 b) = t.intoFieldAlias();
        checkPair(a, b, 77, 77);
        (a, b) = t.intoElementAlias();
        checkPair(a, b, 66, 66);
    }

    function testValueAndStorageControls() public {
        MemoryAliasFixes t = new MemoryAliasFixes();
        (uint256 a, uint256 b) = t.valueCopyControl();
        checkPair(a, b, 1, 7);
        (a, b) = t.valueElementCopyControl();
        checkPair(a, b, 5, 9);
        (a, b) = t.storageToMemoryIndependence();
        checkPair(a, b, 1, 100);
        uint256[] memory inp = new uint256[](1);
        inp[0] = 1;
        (a, b) = t.memoryToStorageIndependence(inp);
        checkPair(a, b, 1, 7);
    }

    function testNestedMemoryEncodeDoesNotRevert() public {
        MemoryAliasFixes t = new MemoryAliasFixes();
        require(t.encodeBytesArray() == 1, "encBytesArr");
        require(t.encodeUintMatrix() == 1, "encMatrix");
        require(t.encodeStringArray() == 1, "encStrArr");
        require(t.encodeBytesArrayLength() == 256, "encBytesArrLen");
        require(t.encodeUintMatrixLength() == 288, "encMatrixLen");
    }
}
