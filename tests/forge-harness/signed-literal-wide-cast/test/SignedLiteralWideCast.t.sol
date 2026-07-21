// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {SignedLiteralWideCastTarget} from "../src/SignedLiteralWideCast.sol";

contract SignedLiteralWideCastForgeTest {
    function testCastAddLit() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castAddLit(3) == 13, "cast13");
        require(t.castAddLit(-20) == type(uint256).max - 9, "castWrap");
    }
    function testCastMulLit() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castMulLit(3) == 6, "castMul6");
    }
    function testCastLitAdd() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castLitAdd(3) == 13, "castLitAdd13");
    }
    function testCastInt128() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castInt128(3) == 13, "int128add");
        require(t.castInt128(-30) == -20, "int128neg");
    }
    function testNegMulLit() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.negMulLit(3) == -6, "negMul");
    }
    function testNegNested() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.negNested(3, 1) == -1, "negNested");
    }
    function testCastNeg() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castNeg(3) == -6, "castNeg");
    }
    function testCastAddLitOverflowPanics() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("castAddLit(int256)", type(int256).max));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testNegOfMinPanics() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("negMulOne(int256)", type(int256).min));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testInt128OverflowPanics() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("castInt128(int128)", type(int128).max));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testControls() public {
        SignedLiteralWideCastTarget t = new SignedLiteralWideCastTarget();
        require(t.castTwoTyped(3, 4) == 7, "twoTyped");
        require(t.castTwoTyped(-3, 1) == type(uint256).max - 1, "twoTypedWrap");
        require(t.negNoLit(5, 2) == -3, "negNoLit");
        require(t.castBare(-1) == type(uint256).max, "bare");
        require(t.castUnsigned(5) == 15, "unsigned");
    }
}
