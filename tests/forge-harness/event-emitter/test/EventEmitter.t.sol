// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EventEmitterHarnessTarget} from "../src/EventEmitter.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EventEmitterForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    EventEmitterHarnessTarget private target =
        new EventEmitterHarnessTarget();

    function testFireEmitsExpectedLog() public {
        vm.recordLogs();
        target.fire(4, 9);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("Hit(uint256,uint256)"),
            "topic0"
        );
        require(entries[0].topics[1] == bytes32(uint256(4)), "topic1");
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(uint256(9))),
            "data"
        );
    }
}
