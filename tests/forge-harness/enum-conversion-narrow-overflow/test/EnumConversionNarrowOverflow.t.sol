// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import "../src/EnumConversionNarrowOverflow.sol";

contract EnumConversionNarrowOverflowTest {
    function panicCode(bytes memory data) private pure returns (uint256 code) {
        require(data.length == 36);
        assembly { code := mload(add(data, 36)) }
    }

    function testNarrowOverflowPrecedesEnumRangeCheck() public {
        EnumConversionNarrowOverflow c = new EnumConversionNarrowOverflow();
        (bool ok, bytes memory data) = address(c).call(abi.encodeCall(c.run, ()));
        require(!ok && panicCode(data) == 0x11);
    }

    function testSafeAndRangeControls() public {
        EnumConversionNarrowOverflow c = new EnumConversionNarrowOverflow();
        require(c.safe() == 2);
        (bool ok, bytes memory data) = address(c).call(abi.encodeCall(c.rangeOnly, ()));
        require(!ok && panicCode(data) == 0x21);
    }
}
