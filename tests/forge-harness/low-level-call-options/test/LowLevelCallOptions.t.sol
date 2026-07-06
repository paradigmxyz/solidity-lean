// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/LowLevelCallOptions.sol";

contract LowLevelCallOptionsForgeTest {
    function testRawCallPassesValueGasAndPayload() public {
        LowLevelCallOptionsTarget target = new LowLevelCallOptionsTarget();
        LowLevelCallOptionsCaller caller = new LowLevelCallOptionsCaller();
        bytes memory payload =
            abi.encodeWithSelector(
                LowLevelCallOptionsTarget.echo.selector,
                bytes(hex"010203")
            );

        (bool success, bytes memory output) =
            caller.rawCall{value: 5}(payable(address(target)), payload);

        require(success, "success");
        require(
            keccak256(abi.decode(output, (bytes))) ==
                keccak256(bytes(hex"010203")),
            "output"
        );
    }

    function testRawStaticUsesStaticcallGasAndPayload() public {
        LowLevelCallOptionsTarget target = new LowLevelCallOptionsTarget();
        LowLevelCallOptionsCaller caller = new LowLevelCallOptionsCaller();
        bytes memory payload =
            abi.encodeWithSelector(LowLevelCallOptionsTarget.read.selector);

        (bool success, bytes memory output) =
            caller.rawStatic(address(target), payload);

        require(success, "success");
        require(abi.decode(output, (uint256)) == 77, "output");
    }
}
