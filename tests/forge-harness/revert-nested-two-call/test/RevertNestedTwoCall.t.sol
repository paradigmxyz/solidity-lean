// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RevertNestedTwoCallHarnessTarget} from "../src/RevertNestedTwoCall.sol";

interface Vm {
    function expectRevert(bytes calldata revertData) external;
}

contract RevertNestedTwoCallForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    RevertNestedTwoCallHarnessTarget private target =
        new RevertNestedTwoCallHarnessTarget();

    function testGoRevertsWithFullyEncodedNestedError() public {
        uint256[][] memory m = new uint256[][](1);
        m[0] = new uint256[](1);
        m[0][0] = 4;
        vm.expectRevert(
            abi.encodeWithSignature(
                "Nested(uint256[][],string)", m, "qq"
            )
        );
        target.go();
    }
}
