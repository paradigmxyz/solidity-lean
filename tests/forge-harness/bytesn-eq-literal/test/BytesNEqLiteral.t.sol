// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/BytesNEqLiteral.sol";

contract BytesNEqLiteralForgeTest {
    BytesNEqLiteral private target;

    function setUp() public {
        target = new BytesNEqLiteral();
    }

    function testEqStringLiteral() public view {
        require(target.a(0x61626364) == true);
        require(target.a(0x00000000) == false);
    }

    function testNeHexLiteral() public view {
        require(target.b(0x12340000) == false);
        require(target.b(0x00000000) == true);
    }

    function testEqShorterHexLiteral() public view {
        require(target.c(bytes32(0)) == true);
        require(target.c(bytes32(uint256(1))) == false);
    }
}
