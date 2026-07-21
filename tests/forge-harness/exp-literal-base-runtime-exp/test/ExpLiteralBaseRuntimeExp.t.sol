// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExpLiteralBaseRuntimeExpTarget} from "../src/ExpLiteralBaseRuntimeExp.sol";

contract ExpLiteralBaseRuntimeExpForgeTest {
    function testLitUintNoPanic() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.litUint(8) == 256, "lit2p8");
        require(t.litUint(255) == 2 ** 255, "lit2p255");
    }
    function testLitIntNoPanic() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.litInt(9) == -512, "litNeg2p9");
        require(t.litInt(8) == 256, "litNeg2p8");
    }
    function testLitUintOverflowPanics() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("litUintWide(uint16)", 256));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testFoldControls() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.foldQ112() == 2 ** 112, "q112");
        require(t.fold255() == 2 ** 255, "fold255");
        require(t.foldNeg255() == type(int256).min, "foldNeg255");
    }
    function testShiftControl() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.shiftLit(200) == (uint256(1) << 200), "shift200");
    }
    function testTypedSignedControl() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.typedSigned(9) == -512, "typedNeg2p9");
    }
    function testNarrowTypedValue() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        require(t.narrowTyped(2, 7) == 128, "narrow2p7");
    }
    function testNarrowTypedPanics() public {
        ExpLiteralBaseRuntimeExpTarget t = new ExpLiteralBaseRuntimeExpTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("narrowTyped(uint8,uint8)", 2, 8));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
}
