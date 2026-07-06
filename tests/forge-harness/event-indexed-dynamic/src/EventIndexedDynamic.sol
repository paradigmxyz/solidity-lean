// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract EventIndexedDynamicHarnessTarget {
    struct Pair {
        uint8 a;
        uint16 b;
    }

    struct Packet {
        uint8 tag;
        bytes body;
    }

    event Blob(bytes indexed key, string indexed label, bytes payload);
    event Words(string indexed label) anonymous;
    event Composite(uint8[] indexed small, Pair indexed pair, bytes payload);
    event Fixed(uint8[2] indexed pair, bytes payload);
    event Nested(Packet indexed packet, bytes payload);
    event Chunks(bytes[] indexed chunks, bytes payload);
    event PacketList(Packet[] indexed packets, bytes payload);

    function fire(bytes calldata key, string calldata label, bytes calldata payload)
        external
    {
        emit Blob(key, label, payload);
    }

    function fireAnonymous(string calldata label) external {
        emit Words(label);
    }

    function fireComposite(
        uint8[] calldata small,
        uint8 a,
        uint16 b,
        bytes calldata payload
    ) external {
        emit Composite(small, Pair({a: a, b: b}), payload);
    }

    function fireFixed(uint8[2] calldata pair, bytes calldata payload) external {
        emit Fixed(pair, payload);
    }

    function fireNested(uint8 tag, bytes calldata body, bytes calldata payload)
        external
    {
        emit Nested(Packet({tag: tag, body: body}), payload);
    }

    function fireChunks(bytes[] calldata chunks, bytes calldata payload) external {
        emit Chunks(chunks, payload);
    }

    function firePacketList(Packet[] calldata packets, bytes calldata payload)
        external
    {
        emit PacketList(packets, payload);
    }
}
