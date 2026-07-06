// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/PointerReturnDefinite.sol";

contract PointerReturnDefiniteForgeTest {
    PointerReturnDefinite private target;

    function setUp() public {
        target = new PointerReturnDefinite();
    }

    function testStoragePointerReturnPaths() public {
        require(target.runStorage(true) == 11, "branch first");
        require(target.runStorage(false) == 22, "branch second");
        require(target.runExplicit(true) == 11, "explicit first");
        require(target.runExplicit(false) == 22, "explicit second");
        require(target.runDoOnce() == 11, "do while");
        require(target.runModified() == 22, "modified storage");
    }

    function testCalldataPointerReturnPaths() public view {
        uint256[] memory left = new uint256[](1);
        uint256[] memory right = new uint256[](1);
        left[0] = 33;
        right[0] = 44;

        require(target.runCalldata(true, left, right) == 33, "calldata left");
        require(target.runCalldata(false, left, right) == 44, "calldata right");
    }
}
