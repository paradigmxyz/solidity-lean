// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CallposRemainderHarnessTarget} from "../src/CallposRemainder.sol";

contract CallposRemainderForgeTest {
    CallposRemainderHarnessTarget private target =
        new CallposRemainderHarnessTarget();

    // Bug 1 — internal call in `+=` RHS on a plain state var.
    function testAddInternal() public {
        require(target.addInternal() == 42, "kk += fee() must equal 42");
    }

    // Bug 1 — eval-order pin: call runs before the LValue read (kk = 100, +1).
    function testOrderInternal() public {
        require(target.orderInternal() == 101, "kk += bump() must equal 101");
    }

    // Bug 1 — internal call in `+=` RHS on a mapping LValue.
    function testMapAddInternal() public {
        require(target.mapAddInternal() == 42, "mm[3] += fee() must equal 42");
    }

    // Bug 1 — mapping-LValue eval-order pin: setK() runs before the index read.
    function testMapOrderInternal() public {
        require(target.mapOrderInternal() == 17, "mm[kk] += setK() must equal 17");
    }

    // Bug 1 — narrow (uint8) `+=` with a call RHS, in range.
    function testNarrowInRange() public {
        require(target.narrowInRange() == 155, "narrow += must equal 155");
    }

    // Bug 1 — narrow (uint8) `+=` with a call RHS overflows -> Panic 0x11.
    function testNarrowOverflowPanics() public {
        try target.narrowOverflow() returns (uint8) {
            revert("expected narrow += overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong narrow += overflow panic");
        }
    }

    // Bug 1 — narrow (uint8) `<<=` with a call RHS truncates to 0.
    function testNarrowShlCall() public {
        require(target.narrowShlCall() == 0, "narrow <<= call must truncate to 0");
    }

    // Bug 2 — storage array `.push(<internal call>)`.
    function testPushInternal() public {
        require(target.pushInternal() == 37, "xs.push(fee()) must store 37");
    }

    // Bug 1 — control: call-free compound-assign unchanged.
    function testPlainCompoundControl() public {
        require(target.plainCompoundControl() == 15, "plain += must equal 15");
    }

    // Bug 2 — control: call-free push unchanged.
    function testPlainPushControl() public {
        require(target.plainPushControl() == 9, "plain push must store 9");
    }

    // Bug 1 — external `this.g()` in `+=` RHS.
    function testAddExternal() public {
        require(target.addExternal() == 42, "kk += this.g() must equal 42");
    }

    // Bug 2 — storage array `.push(this.g())` (external).
    function testPushExternal() public {
        require(target.pushExternal() == 37, "xs.push(this.g()) must store 37");
    }
}
