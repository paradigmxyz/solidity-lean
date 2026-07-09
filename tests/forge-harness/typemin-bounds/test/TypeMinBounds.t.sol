// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/TypeMinBounds.sol";

contract TypeMinBoundsForgeTest {
    TypeMinBounds private target;

    function setUp() public {
        target = new TypeMinBounds();
    }

    function testInt8MinIsNeg128() public view {
        require(target.int8Min() == -128);
        require(target.int8Min() == type(int8).min);
    }

    function testInt128MinIsTwosComplement() public view {
        require(target.int128Min() == type(int128).min);
        require(target.int128Min() == -170141183460469231731687303715884105728);
    }

    function testInt256MinIsTwosComplement() public view {
        require(target.int256Min() == type(int256).min);
    }

    function testInt8MinNarrow() public view {
        require(target.int8MinNarrow() == type(int8).min);
        require(target.int8MinNarrow() == -128);
    }

    function testInt128MinNarrow() public view {
        require(target.int128MinNarrow() == type(int128).min);
    }

    function testInt8MinEqualsNeg128() public view {
        require(target.int8MinEqNeg128() == true);
    }

    function testInt8MinPlusOne() public view {
        require(target.int8MinPlusOne() == -127);
    }
}
