// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EmitMemoryNestedHarnessTarget} from "../src/EmitMemoryNested.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EmitMemoryNestedForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    EmitMemoryNestedHarnessTarget private target =
        new EmitMemoryNestedHarnessTarget();

    function testRunEmitsNestedArrayLog() public {
        vm.recordLogs();
        target.run();
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 1, "topic count");
        require(
            entries[0].topics[0] == keccak256("N(uint256[][])"),
            "topic0"
        );
        uint256[][] memory rows = new uint256[][](2);
        rows[0] = new uint256[](1);
        rows[0][0] = 7;
        rows[1] = new uint256[](2);
        rows[1][0] = 8;
        rows[1][1] = 9;
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(rows)),
            "data"
        );
    }
}
