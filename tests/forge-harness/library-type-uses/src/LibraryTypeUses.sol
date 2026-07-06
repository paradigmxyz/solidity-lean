// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library LibraryTypeToken {}

contract LibraryTypeUses {
    function libraryAddress(address input)
        external
        pure
        returns (address)
    {
        return address(LibraryTypeToken(input));
    }

    function libraryName() external pure returns (string memory) {
        return type(LibraryTypeToken).name;
    }
}
