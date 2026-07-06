// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/LibraryTypeUses.sol";

contract LibraryTypeUsesForgeTest {
    LibraryTypeUses private target;

    function setUp() public {
        target = new LibraryTypeUses();
    }

    function testTransientLibraryTypeExpressions() public view {
        require(target.libraryAddress(address(0x1234)) == address(0x1234));
        require(
            keccak256(bytes(target.libraryName()))
                == keccak256(bytes("LibraryTypeToken"))
        );
    }
}
