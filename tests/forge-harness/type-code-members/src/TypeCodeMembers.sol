// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ConcreteCodeTarget {
    function marker() external pure returns (uint256) {
        return 1;
    }
}

library LibraryCodeTarget {}

contract TypeCodeMembers {
    function contractCreationLength() external pure returns (uint256) {
        return type(ConcreteCodeTarget).creationCode.length;
    }

    function contractRuntimeLength() external pure returns (uint256) {
        return type(ConcreteCodeTarget).runtimeCode.length;
    }

    function libraryCreationLength() external pure returns (uint256) {
        return type(LibraryCodeTarget).creationCode.length;
    }

    function libraryRuntimeLength() external pure returns (uint256) {
        return type(LibraryCodeTarget).runtimeCode.length;
    }

    function contractNameLength() external pure returns (uint256) {
        return bytes(type(ConcreteCodeTarget).name).length;
    }

    function libraryNameLength() external pure returns (uint256) {
        return bytes(type(LibraryCodeTarget).name).length;
    }
}
