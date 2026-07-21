// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {OperatorUdvtResolutionHarnessTarget}
    from "../src/OperatorUdvtResolution.sol";

contract OperatorUdvtResolutionForgeTest {
    OperatorUdvtResolutionHarnessTarget private t =
        new OperatorUdvtResolutionHarnessTarget();

    function testOpAdd() public view {
        require(t.opAdd(3, 4) == 7, "opAdd");
    }

    function testOpChain() public view {
        require(t.opChain(3, 4, 5) == 12, "opChain");
    }

    function testOpMixed() public view {
        // -(3 + 4) - 5 on uint128 wraps: 0 - 7 panics? ptNeg does
        // Pt.wrap(0) - a via ptSub (checked uint128) -> 0 - 7 Panics 0x11.
        // Use values where it stays in range: a=0,b=0,c=0 -> 0.
        require(t.opMixed(0, 0, 0) == 0, "opMixed zero");
    }

    function testOpMixedPanics() public {
        (bool ok, bytes memory data) = address(t).staticcall(
            abi.encodeWithSignature(
                "opMixed(uint128,uint128,uint128)",
                uint128(3), uint128(4), uint128(5)));
        require(!ok, "opMixed must panic");
        require(data.length == 36 && uint8(data[35]) == 0x11,
            "opMixed panic 0x11");
    }

    function testOpStorage() public {
        require(t.opStorage(41) == 42, "opStorage");
    }

    function testOpTernary() public view {
        require(t.opTernary(10, 20, true) == 12, "opTernary true");
        require(t.opTernary(10, 20, false) == 22, "opTernary false");
    }

    function testOpEqChain() public view {
        require(t.opEqChain(5, 6), "opEqChain");
    }

    function testOpCallOperand() public view {
        require(t.opCallOperand(8, 9) == 17, "opCallOperand");
    }
}
