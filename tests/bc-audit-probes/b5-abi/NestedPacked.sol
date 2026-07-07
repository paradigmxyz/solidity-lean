// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc REJECTS nested dynamic array in abi.encodePacked (Type ... not supported
// in packed mode). Over-accept probe.
contract NestedPacked {
    function packNested() external pure returns (bytes memory) {
        uint256[][] memory a = new uint256[][](1);
        a[0] = new uint256[](1);
        a[0][0] = 1;
        return abi.encodePacked(a);
    }
}
