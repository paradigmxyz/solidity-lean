// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../src/OpenZeppelinMulticall.sol";

contract OpenZeppelinMulticallForgeTest {
    function testMulticallDelegatecallsSelfAndReturnsData() public {
        OpenZeppelinMulticallHarness harness =
            new OpenZeppelinMulticallHarness(address(0));
        bytes[] memory calls = new bytes[](2);
        calls[0] = abi.encodeWithSelector(harness.setValue.selector, 7);
        calls[1] = abi.encodeWithSelector(harness.addValue.selector, 5);

        bytes[] memory results = harness.multicall(calls);

        require(results.length == 2, "results length");
        require(abi.decode(results[0], (uint256)) == 8, "set return");
        require(abi.decode(results[1], (uint256)) == 12, "add return");
        require(harness.value() == 12, "stored value");
    }

    function testForwardedContextSuffixPropagatesToSubcall() public {
        address forwarder = address(0xf0);
        address user = address(0xa11ce);
        OpenZeppelinMulticallHarness harness =
            new OpenZeppelinMulticallHarness(forwarder);
        bytes[] memory calls = new bytes[](1);
        calls[0] = abi.encodeWithSelector(
            harness.exposedSenderDataLength.selector
        );
        bytes memory forwarded = bytes.concat(
            abi.encodeWithSelector(harness.multicall.selector, calls),
            bytes20(user)
        );

        Vm vm = _vm();
        vm.prank(forwarder);
        (bool success, bytes memory output) = address(harness).call(forwarded);
        require(success, "forwarded multicall");

        bytes[] memory results = abi.decode(output, (bytes[]));
        require(results.length == 1, "forwarded results length");
        (address sender, uint256 dataLength) =
            abi.decode(results[0], (address, uint256));
        require(sender == user, "forwarded sender");
        require(dataLength == calls[0].length, "stripped subcall data");
    }

    function testDelegatecallFailureReverts() public {
        OpenZeppelinMulticallHarness harness =
            new OpenZeppelinMulticallHarness(address(0));
        bytes[] memory calls = new bytes[](1);
        calls[0] = abi.encodeWithSelector(harness.fail.selector);

        (bool success, bytes memory output) = address(harness).call(
            abi.encodeWithSelector(harness.multicall.selector, calls)
        );
        require(!success, "failed");
        require(
            keccak256(output) ==
                keccak256(
                    abi.encodeWithSignature(
                        "Error(string)",
                        "Address: low-level delegate call failed"
                    )
                ),
            "revert reason"
        );
    }

    function _vm() private pure returns (Vm) {
        return Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    }
}

interface Vm {
    function prank(address sender) external;
}
