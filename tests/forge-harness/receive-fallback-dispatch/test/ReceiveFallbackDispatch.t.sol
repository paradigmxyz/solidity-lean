// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/ReceiveFallbackDispatch.sol";

contract ReceiveFallbackDispatchForgeTest {
    function requireSnapshot(
        ReceiveFallbackDispatch target,
        uint256 expectedMarker,
        address expectedSender,
        uint256 expectedValue,
        uint256 expectedDataLength
    ) internal view {
        (
            uint256 marker,
            address sender,
            uint256 value,
            uint256 dataLength
        ) = target.snapshot();
        require(marker == expectedMarker, "marker");
        require(sender == expectedSender, "sender");
        require(value == expectedValue, "value");
        require(dataLength == expectedDataLength, "data length");
    }

    function testReceiveFallbackAndSelectorPrecedence() public {
        ReceiveFallbackDispatch target = new ReceiveFallbackDispatch();

        (bool receiveOk, bytes memory receiveOutput) =
            address(target).call("");
        require(receiveOk, "receive");
        require(receiveOutput.length == 0, "receive output");
        requireSnapshot(target, 2, address(this), 0, 0);

        bytes memory fallbackPayload = hex"deadbeef0102";
        (bool fallbackOk, bytes memory fallbackOutput) =
            address(target).call(fallbackPayload);
        require(fallbackOk, "fallback");
        require(fallbackOutput.length == 0, "fallback output");
        requireSnapshot(target, 1, address(this), 0, fallbackPayload.length);
        require(
            keccak256(target.lastData()) == keccak256(fallbackPayload),
            "fallback data"
        );

        bytes memory functionPayload =
            abi.encodeCall(ReceiveFallbackDispatch.touch, (9));
        (bool functionOk, bytes memory functionOutput) =
            address(target).call(functionPayload);
        require(functionOk, "function");
        require(abi.decode(functionOutput, (uint256)) == 10, "function out");
        requireSnapshot(target, 9, address(this), 0, fallbackPayload.length);
    }

    function testTypedFallbackReturnsRawCalldata() public {
        ReceiveFallbackBytes target = new ReceiveFallbackBytes();
        bytes memory payload = hex"0102030405";

        (bool ok, bytes memory output) = address(target).call(payload);
        require(ok, "typed fallback");
        require(keccak256(output) == keccak256(payload), "raw output");
    }

    function testReceiveFallbackMissingBoundaries() public {
        ReceiveFallbackOnlyFallback onlyFallback =
            new ReceiveFallbackOnlyFallback();
        (bool fallbackOk, bytes memory fallbackOutput) =
            address(onlyFallback).call("");
        require(fallbackOk, "only fallback empty");
        require(fallbackOutput.length == 0, "only fallback output");
        require(onlyFallback.marker() == 3, "only fallback marker");

        ReceiveFallbackOnlyReceive onlyReceive =
            new ReceiveFallbackOnlyReceive();
        (bool receiveOk, bytes memory receiveOutput) =
            address(onlyReceive).call("");
        require(receiveOk, "only receive empty");
        require(receiveOutput.length == 0, "only receive output");
        require(onlyReceive.marker() == 4, "only receive marker");

        (bool missingFallbackOk, bytes memory missingFallbackOutput) =
            address(onlyReceive).call(hex"deadbeef");
        require(!missingFallbackOk, "missing fallback");
        require(missingFallbackOutput.length == 0, "missing fallback output");

        ReceiveFallbackMissing missing = new ReceiveFallbackMissing();
        (bool unknownOk, bytes memory unknownOutput) =
            address(missing).call(hex"deadbeef");
        require(!unknownOk, "unknown selector");
        require(unknownOutput.length == 0, "unknown output");

        (bool emptyOk, bytes memory emptyOutput) = address(missing).call("");
        require(!emptyOk, "missing receive");
        require(emptyOutput.length == 0, "empty output");
    }

    function testInheritedAndOverriddenDispatch() public {
        ReceiveFallbackChild child = new ReceiveFallbackChild();
        (bool childReceiveOk,) = address(child).call("");
        require(childReceiveOk, "child receive");
        require(child.marker() == 5, "child receive marker");

        (bool childFallbackOk,) = address(child).call(hex"deadbeef");
        require(childFallbackOk, "child fallback");
        require(child.marker() == 6, "child fallback marker");

        ReceiveFallbackOverride overrideTarget = new ReceiveFallbackOverride();
        (bool overrideReceiveOk,) = address(overrideTarget).call("");
        require(overrideReceiveOk, "override receive");
        require(overrideTarget.marker() == 7, "override receive marker");

        (bool overrideFallbackOk,) =
            address(overrideTarget).call(hex"deadbeef");
        require(overrideFallbackOk, "override fallback");
        require(overrideTarget.marker() == 8, "override fallback marker");
    }
}
