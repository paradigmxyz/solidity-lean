// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinERC2771Context.sol";

contract OpenZeppelinERC2771ContextForgeTest {
    function testTrustedForwarderAndDirectContext() public {
        address forwarder = address(0xf0);
        OpenZeppelinERC2771ContextHarness harness =
            new OpenZeppelinERC2771ContextHarness(forwarder);

        require(harness.trustedForwarder() == forwarder, "forwarder");
        require(harness.isTrustedForwarder(forwarder), "trusted");
        require(!harness.isTrustedForwarder(address(0xbad)), "untrusted");
        require(harness.exposedContextSuffixLength() == 20, "suffix");

        bytes memory expected = abi.encodeWithSelector(
            harness.exposedData.selector
        );
        require(_eq(harness.exposedData(), expected), "direct data");
        require(harness.exposedSender() == address(this), "direct sender");
    }

    function testForwardedSenderAndDataStripsSuffix() public {
        address forwarder = address(0xf0);
        address user = address(0xa11ce);
        OpenZeppelinERC2771ContextHarness harness =
            new OpenZeppelinERC2771ContextHarness(forwarder);
        bytes memory payload = hex"01020304";
        bytes memory baseCall = abi.encodeWithSelector(
            harness.exposedSenderDataAndPayloadLength.selector,
            payload
        );
        bytes memory forwarded = bytes.concat(baseCall, bytes20(user));

        Vm vm = _vm();
        vm.prank(forwarder);
        (bool success, bytes memory output) = address(harness).staticcall(
            forwarded
        );
        require(success, "forwarded call");

        (address sender, bytes memory data, uint256 payloadLength) =
            abi.decode(output, (address, bytes, uint256));
        require(sender == user, "forwarded sender");
        require(_eq(data, baseCall), "forwarded data");
        require(payloadLength == payload.length, "payload length");
    }

    function testUntrustedForwarderDoesNotStripSuffix() public {
        address forwarder = address(0xf0);
        address attacker = address(0xbad);
        address user = address(0xa11ce);
        OpenZeppelinERC2771ContextHarness harness =
            new OpenZeppelinERC2771ContextHarness(forwarder);
        bytes memory baseCall = abi.encodeWithSelector(
            harness.exposedSender.selector
        );
        bytes memory appended = bytes.concat(baseCall, bytes20(user));

        Vm vm = _vm();
        vm.prank(attacker);
        (bool success, bytes memory output) = address(harness).staticcall(
            appended
        );
        require(success, "untrusted call");

        address sender = abi.decode(output, (address));
        require(sender == attacker, "untrusted sender");

        vm.prank(attacker);
        (success, output) = address(harness).staticcall(
            bytes.concat(
                abi.encodeWithSelector(harness.exposedData.selector),
                bytes20(user)
            )
        );
        require(success, "untrusted data call");
        bytes memory data = abi.decode(output, (bytes));
        require(
            _eq(
                data,
                bytes.concat(
                    abi.encodeWithSelector(harness.exposedData.selector),
                    bytes20(user)
                )
            ),
            "untrusted data"
        );
    }

    function testTrustedForwarderShortCalldataFallsBackToForwarder() public {
        address forwarder = address(0xf0);
        OpenZeppelinERC2771ContextHarness harness =
            new OpenZeppelinERC2771ContextHarness(forwarder);
        bytes memory callData = abi.encodeWithSelector(
            harness.exposedSender.selector
        );

        Vm vm = _vm();
        vm.prank(forwarder);
        (bool success, bytes memory output) = address(harness).staticcall(
            callData
        );
        require(success, "short call");

        address sender = abi.decode(output, (address));
        require(sender == forwarder, "short sender");
    }

    function _eq(bytes memory left, bytes memory right)
        private
        pure
        returns (bool)
    {
        return keccak256(left) == keccak256(right);
    }

    function _vm() private pure returns (Vm) {
        return Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    }
}

interface Vm {
    function prank(address sender) external;
}
