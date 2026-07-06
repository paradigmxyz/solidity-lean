// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReferenceViaIrMemoryStorage.sol";

contract ReferenceViaIrMemoryStorageForgeTest {
    function checkPair(
        uint256 actualX,
        uint256 actualY,
        uint256 expectedX,
        uint256 expectedY
    ) internal pure {
        require(actualX == expectedX, "first");
        require(actualY == expectedY, "second");
    }

    function testMemoryStructArrayToStorageCopy() public {
        ReferenceViaIrMemoryStorage target =
            new ReferenceViaIrMemoryStorage();
        ReferenceViaIrMemoryStorage.Blob[] memory blobs =
            new ReferenceViaIrMemoryStorage.Blob[](2);
        blobs[0] = ReferenceViaIrMemoryStorage.Blob({
            data: hex"0102",
            tag: 3
        });
        blobs[1] = ReferenceViaIrMemoryStorage.Blob({
            data: hex"0304",
            tag: 4
        });

        (uint256 storedSum, uint256 memorySum) =
            target.memoryStructArrayToStorageCopy(blobs);
        checkPair(storedSum, memorySum, 5, 106);
    }
}
