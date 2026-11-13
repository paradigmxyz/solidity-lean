// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {FixedBytesConstantWidthsHarnessTarget} from "../src/FixedBytesConstantWidths.sol";

contract FixedBytesConstantWidthsForgeTest {
    FixedBytesConstantWidthsHarnessTarget private target =
        new FixedBytesConstantWidthsHarnessTarget();

    function testCompared() public view {
        require(target.compared(), "bytes2 constant == bytes4 constant");
    }

    function testWidenedCompare() public view {
        require(target.widenedCompare(), "bytes4 constant == bytes8 constant");
    }

    function testWidened() public view {
        require(target.widened() == bytes4(0x12340000), "bytes2 constant widened");
    }

    function testCombined() public view {
        require(target.combined() == bytes4(0x12345678), "bytes4 | bytes2 constant");
    }

    function testSelected() public view {
        require(target.selected() == bytes4(0x12340000), "conditional of constants");
    }

    function testCompareParam() public view {
        require(target.compareParam(bytes4(0x12340000)), "constant == parameter");
    }

    function testConstantLength() public view {
        require(target.constantLength() == 4, "constant .length");
    }

    function testPackedHash() public view {
        require(target.packedHash() == keccak256(hex"123412"), "packed constants");
    }

    function testEncodedHash() public view {
        require(
            target.encodedHash() == keccak256(abi.encode(bytes2(0x1234))),
            "encoded constant"
        );
    }

    function testSideEffect() public {
        (uint256 length, uint256 calls) = target.sideEffect();
        require(length == 4 && calls == 1, "f().length runs f");
        (length, calls) = target.sideEffect();
        require(length == 4 && calls == 2, "f().length runs f again");
    }
}
