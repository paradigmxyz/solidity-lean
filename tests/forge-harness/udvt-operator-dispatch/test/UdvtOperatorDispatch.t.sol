// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {UdvtOperatorDispatch} from "../src/UdvtOperatorDispatch.sol";

contract UdvtOperatorDispatchForgeTest {
    UdvtOperatorDispatch private target = new UdvtOperatorDispatch();

    // Fixed-point multiply differs from the built-in `*`: 500e18 + 500e18 * 0.1
    // (fixed-point) == 550e18. The built-in-`*` bug would return ~5e37.
    function testApplyInterest() public view {
        require(
            target.applyInterest(500e18, 1e17) == 550e18,
            "applyInterest fixed-point mismatch"
        );
    }

    function testDoubleNeg() public view {
        require(target.doubleNeg(7e18) == 7e18, "double unary neg not identity");
    }

    function testDiff() public view {
        require(target.diff(9e18, 4e18) == 5e18, "binary minus mismatch");
    }

    function testComparisonOperators() public view {
        require(target.less(3e18, 4e18), "less true case");
        require(!target.less(4e18, 3e18), "less false case");
        require(target.equal(4e18, 4e18), "equal true case");
        require(!target.equal(4e18, 5e18), "equal false case");
    }

    // Operator body is checked; the overflow panics 0x11 even though the call
    // site is inside an `unchecked` block.
    function testCheckedOperatorOverflowPanics() public {
        try target.checkedOpOverflow(type(uint256).max) returns (uint256) {
            revert("expected checked operator overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong overflow panic code");
        }
    }

    // Operator body is unchecked; the add wraps modulo 2^256 (max + 1 == 0).
    function testUncheckedOperatorWraps() public view {
        require(
            target.uncheckedOpWraps(type(uint256).max) == 0,
            "unchecked operator did not wrap"
        );
    }
}
