// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReferenceInternalMemoryBoundaries.sol";

contract ReferenceInternalMemoryBoundariesForgeTest {
    function checkPair(
        uint256 actualX,
        uint256 actualY,
        uint256 expectedX,
        uint256 expectedY
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
    }

    function testInternalMemoryReferenceBoundaries() public {
        ReferenceInternalMemoryBoundaries target =
            new ReferenceInternalMemoryBoundaries();

        (uint256 paramX, uint256 paramY) =
            target.internalMemoryParamAlias();
        checkPair(paramX, paramY, 91, 91);

        (uint256 returnX, uint256 returnY) =
            target.internalMemoryReturnAlias();
        checkPair(returnX, returnY, 92, 92);

        (uint256 tupleReturnX, uint256 tupleReturnY) =
            target.internalMemoryTupleReturnAlias();
        checkPair(tupleReturnX, tupleReturnY, 93, 93);

        (uint256 structReturnX, uint256 structReturnY) =
            target.internalMemoryStructReturnAlias();
        checkPair(structReturnX, structReturnY, 94, 94);

        (uint256 bytesParamX, uint256 bytesParamY) =
            target.internalBytesParamAlias();
        checkPair(bytesParamX, bytesParamY, 17, 17);

        (uint256 bytesReturnX, uint256 bytesReturnY) =
            target.internalBytesReturnAlias();
        checkPair(bytesReturnX, bytesReturnY, 18, 18);
    }
}
