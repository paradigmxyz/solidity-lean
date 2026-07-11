// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TupleVarDeclAbiDecodeTarget} from "../src/TupleVarDeclAbiDecode.sol";

contract TupleVarDeclAbiDecodeForgeTest {
    function testAddPair() public {
        TupleVarDeclAbiDecodeTarget t = new TupleVarDeclAbiDecodeTarget();
        bytes memory data = abi.encode(uint256(3), uint256(4));
        require(t.addPair(data) == 7, "addPair");
    }

    function testFirstOfPair() public {
        TupleVarDeclAbiDecodeTarget t = new TupleVarDeclAbiDecodeTarget();
        bytes memory data = abi.encode(uint256(9), uint256(4));
        require(t.firstOfPair(data) == 9, "firstOfPair");
    }

    function testSecondOfPair() public {
        TupleVarDeclAbiDecodeTarget t = new TupleVarDeclAbiDecodeTarget();
        bytes memory data = abi.encode(uint256(9), uint256(4));
        require(t.secondOfPair(data) == 4, "secondOfPair");
    }

    function testHeadAndArray() public {
        TupleVarDeclAbiDecodeTarget t = new TupleVarDeclAbiDecodeTarget();
        uint256[] memory arr = new uint256[](3);
        arr[0] = 11;
        arr[1] = 22;
        arr[2] = 33;
        bytes memory data = abi.encode(uint256(9), arr);
        (uint256 x, uint256 second) = t.headAndArray(data);
        require(x == 9, "headAndArray x");
        require(second == 22, "headAndArray a[1]");
    }
}
