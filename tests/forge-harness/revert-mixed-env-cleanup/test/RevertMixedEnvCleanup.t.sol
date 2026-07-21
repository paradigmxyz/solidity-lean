// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RevertMixedEnvCleanupHarnessTarget} from "../src/RevertMixedEnvCleanup.sol";

interface Vm {
    function expectRevert(bytes calldata revertData) external;
}

contract RevertMixedEnvCleanupForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    RevertMixedEnvCleanupHarnessTarget private target =
        new RevertMixedEnvCleanupHarnessTarget();

    function testOverflowPanics0x11BeforeTheCall() public {
        vm.expectRevert(
            abi.encodeWithSignature("Panic(uint256)", 0x11)
        );
        target.run(200, 100);
    }

    function testNoOverflowRevertsWithHoistedCallValue() public {
        vm.expectRevert(
            abi.encodeWithSignature(
                "Err(uint8,uint256)", uint8(5), uint256(1)
            )
        );
        target.run(2, 3);
    }
}
