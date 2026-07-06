// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/TypeCodeMembers.sol";

contract TypeCodeMembersForgeTest {
    TypeCodeMembers private target;

    function setUp() public {
        target = new TypeCodeMembers();
    }

    function testConcreteAndLibraryCodeMembers() public view {
        require(target.contractCreationLength() > 0);
        require(target.contractRuntimeLength() > 0);
        require(target.libraryCreationLength() > 0);
        require(target.libraryRuntimeLength() > 0);
    }

    function testConcreteAndLibraryNameMembers() public view {
        require(target.contractNameLength() == 18);
        require(target.libraryNameLength() == 17);
    }
}
