// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {
    IEncodeCallCallee,
    EncodeCallSelectorHarnessTarget
} from "../src/EncodeCallSelector.sol";

contract EncodeCallSelectorForgeTest {
    EncodeCallSelectorHarnessTarget private harness =
        new EncodeCallSelectorHarnessTarget();

    // Repro A: arg (uint8) narrower than parameter (uint256). solc derives the
    // selector and the encoding from the DECLARED parameter type foo(uint256).
    function testArgNarrowerThanParamUsesParameterType() public view {
        bytes memory encoded =
            harness.argNarrowerThanParam(IEncodeCallCallee(address(0x1234)));

        // Selector is foo(uint256), not foo(uint8).
        require(bytes4(encoded) == IEncodeCallCallee.foo.selector, "A selector");
        require(bytes4(encoded) == bytes4(0x2fbebd38), "A selector literal");

        // Full calldata: foo(uint256) selector ++ the argument encoded as a
        // 32-byte uint256, even though the argument's static type is uint8.
        bytes memory expected =
            abi.encodeWithSelector(IEncodeCallCallee.foo.selector, uint256(3));
        require(keccak256(encoded) == keccak256(expected), "A bytes");
        require(encoded.length == 36, "A length");
    }

    // Repro B: integer literal against a narrow (uint8) parameter. solc derives
    // the selector and the encoding from the DECLARED parameter type foo(uint8).
    function testLiteralVsNarrowParamUsesParameterType() public view {
        bytes memory encoded = harness.literalVsNarrowParam();

        // Selector is foo(uint8), not foo(uint256).
        require(
            bytes4(encoded) == EncodeCallSelectorHarnessTarget.foo.selector,
            "B selector"
        );
        require(bytes4(encoded) == bytes4(0x11602fb3), "B selector literal");

        // Full calldata: foo(uint8) selector ++ the literal encoded (padded to
        // 32 bytes), not the uint256 default the literal would otherwise take.
        bytes memory expected = abi.encodeWithSelector(
            EncodeCallSelectorHarnessTarget.foo.selector,
            uint8(3)
        );
        require(keccak256(encoded) == keccak256(expected), "B bytes");
        require(encoded.length == 36, "B length");
    }
}
