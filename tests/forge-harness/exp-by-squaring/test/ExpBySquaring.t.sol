// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExpBySquaringTarget} from "../src/ExpBySquaring.sol";

contract ExpBySquaringForgeTest {
    ExpBySquaringTarget private target = new ExpBySquaringTarget();

    function testUncheckedBigExponentWraps() public view {
        // 3 ** (2**200) mod 2**256 — the O(y) hang case.
        require(
            target.uncheckedExp(3, 2 ** 200) ==
                90227379838503308256418949283165379265846182674772648785782829402385907974145,
            "unchecked big exp wrap"
        );
    }

    function testCheckedExpNoOverflow() public view {
        require(target.checkedExp(2, 255) == 2 ** 255, "2**255");
    }

    function testCheckedExpOverflowPanics() public {
        try target.checkedExp(2, 256) returns (uint256) {
            revert("expected exp overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong exp overflow panic");
        }
    }

    function testUncheckedNarrowWraps() public view {
        require(target.uncheckedNarrowWrap(2, 9) == 0, "uint8 2**9 wraps to 0");
        require(target.uncheckedNarrowWrap(3, 5) == 243, "uint8 3**5");
    }

    function testSignedUncheckedNarrowWraps() public view {
        require(target.signedUncheckedNarrowWrap(-2, 9) == 0, "int8 (-2)**9 wraps to 0");
    }

    function testSignedCheckedExp() public view {
        require(target.signedCheckedExp(2, 254) == 2 ** 254, "int256 2**254");
    }

    function testSignedCheckedExpOverflowPanics() public {
        try target.signedCheckedExp(2, 255) returns (int256) {
            revert("expected signed exp overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong signed exp overflow panic");
        }
    }
}
