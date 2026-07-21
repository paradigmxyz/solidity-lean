// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EventOverloadHarnessTarget} from "../src/EventOverload.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EventOverloadForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    EventOverloadHarnessTarget private target =
        new EventOverloadHarnessTarget();

    function testFireWordUsesUintOverload() public {
        vm.recordLogs();
        target.fireWord();
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].topics.length == 1, "topic count");
        require(entries[0].topics[0] == keccak256("E(uint256)"), "topic0");
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(uint256(5))),
            "data"
        );
    }

    function testFireAddrUsesAddressOverload() public {
        vm.recordLogs();
        address a = address(0xABCD);
        target.fireAddr(a);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].topics.length == 1, "topic count");
        require(entries[0].topics[0] == keccak256("E(address)"), "topic0");
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(a)),
            "data"
        );
    }
}
