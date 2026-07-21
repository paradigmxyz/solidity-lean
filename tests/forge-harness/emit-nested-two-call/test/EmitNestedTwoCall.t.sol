// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EmitNestedTwoCallHarnessTarget} from "../src/EmitNestedTwoCall.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EmitNestedTwoCallForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    EmitNestedTwoCallHarnessTarget private target =
        new EmitNestedTwoCallHarnessTarget();

    function testGoEmitsFullyEncodedNestedLog() public {
        vm.recordLogs();
        target.go();
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 1, "topic count");
        require(
            entries[0].topics[0] == keccak256("N2(uint256[][],uint256)"),
            "topic0"
        );
        uint256[][] memory m = new uint256[][](1);
        m[0] = new uint256[](1);
        m[0][0] = 4;
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(m, uint256(9))),
            "data"
        );
    }
}
