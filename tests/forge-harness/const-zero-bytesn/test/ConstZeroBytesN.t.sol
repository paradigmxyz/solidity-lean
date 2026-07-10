// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ConstZeroBytesN.sol";

contract ConstZeroBytesNForgeTest {
    ConstZeroBytesN private target;

    function setUp() public {
        target = new ConstZeroBytesN();
    }

    function testConstFoldZeroIsZeroBytesN() public view {
        require(target.zeroFold() == bytes32(0));
        require(target.zeroFold16() == bytes16(0));
    }

    function testFoldedZeroArgResolvesBytesNOverload() public view {
        require(target.callGWithZeroFold() == 42);
        require(target.g(bytes32(0)) == 42);
    }
}
