// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {EventIndexedDynamicHarnessTarget} from "../src/EventIndexedDynamic.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EventIndexedDynamicForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    EventIndexedDynamicHarnessTarget private target =
        new EventIndexedDynamicHarnessTarget();

    function testDynamicIndexedTopicsAndData() public {
        bytes memory key = hex"010203";
        string memory label = "cat";
        bytes memory payload = hex"0405";

        vm.recordLogs();
        target.fire(key, label, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 3, "topic count");
        require(
            entries[0].topics[0] == keccak256("Blob(bytes,string,bytes)"),
            "topic0"
        );
        require(entries[0].topics[1] == keccak256(key), "topic1");
        require(entries[0].topics[2] == keccak256(bytes(label)), "topic2");
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function testAnonymousDynamicIndexedTopic() public {
        string memory label = "cat";

        vm.recordLogs();
        target.fireAnonymous(label);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 1, "topic count");
        require(entries[0].topics[0] == keccak256(bytes(label)), "topic0");
        require(entries[0].data.length == 0, "data");
    }

    function testIndexedArrayAndStructTopics() public {
        uint8[] memory small = new uint8[](2);
        small[0] = 1;
        small[1] = 2;
        bytes memory payload = hex"090a";

        vm.recordLogs();
        target.fireComposite(small, 7, 0x0203, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 3, "topic count");
        require(
            entries[0].topics[0] ==
                keccak256("Composite(uint8[],(uint8,uint16),bytes)"),
            "topic0"
        );
        require(
            entries[0].topics[1] == keccak256(abi.encode(uint8(1), uint8(2))),
            "topic1"
        );
        require(
            entries[0].topics[2] == keccak256(abi.encode(uint8(7), uint16(0x0203))),
            "topic2"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function testIndexedFixedArrayTopic() public {
        uint8[2] memory pair = [uint8(3), uint8(4)];
        bytes memory payload = hex"0b0c";

        vm.recordLogs();
        target.fireFixed(pair, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("Fixed(uint8[2],bytes)"),
            "topic0"
        );
        require(
            entries[0].topics[1] == keccak256(abi.encode(uint8(3), uint8(4))),
            "topic1"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function testIndexedStructWithDynamicMemberTopic() public {
        bytes memory body = hex"0d0e";
        bytes memory payload = hex"0f10";

        vm.recordLogs();
        target.fireNested(5, body, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("Nested((uint8,bytes),bytes)"),
            "topic0"
        );
        require(
            entries[0].topics[1] ==
                keccak256(bytes.concat(abi.encode(uint8(5)), padRightWord(body))),
            "topic1"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function testIndexedDynamicBytesArrayTopic() public {
        bytes[] memory chunks = new bytes[](2);
        chunks[0] = hex"11";
        chunks[1] = hex"1213";
        bytes memory payload = hex"1415";

        vm.recordLogs();
        target.fireChunks(chunks, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("Chunks(bytes[],bytes)"),
            "topic0"
        );
        require(
            entries[0].topics[1] ==
                keccak256(bytes.concat(padRightWord(chunks[0]), padRightWord(chunks[1]))),
            "topic1"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function testIndexedDynamicStructArrayTopic() public {
        EventIndexedDynamicHarnessTarget.Packet[] memory packets =
            new EventIndexedDynamicHarnessTarget.Packet[](2);
        packets[0] = EventIndexedDynamicHarnessTarget.Packet({
            tag: 6,
            body: hex"2122"
        });
        packets[1] = EventIndexedDynamicHarnessTarget.Packet({
            tag: 7,
            body: hex"23"
        });
        bytes memory payload = hex"2425";

        vm.recordLogs();
        target.firePacketList(packets, payload);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(target), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("PacketList((uint8,bytes)[],bytes)"),
            "topic0"
        );
        require(
            entries[0].topics[1] ==
                keccak256(
                    bytes.concat(
                        abi.encode(uint8(6)),
                        padRightWord(packets[0].body),
                        abi.encode(uint8(7)),
                        padRightWord(packets[1].body)
                    )
                ),
            "topic1"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(payload)),
            "data"
        );
    }

    function padRightWord(bytes memory input) private pure returns (bytes memory out) {
        uint256 paddedLength = ((input.length + 31) / 32) * 32;
        out = new bytes(paddedLength);
        for (uint256 i = 0; i < input.length; i++) {
            out[i] = input[i];
        }
    }
}
