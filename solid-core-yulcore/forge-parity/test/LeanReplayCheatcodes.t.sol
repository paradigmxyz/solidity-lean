// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface ReplayVm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function deal(address target, uint256 newBalance) external;
    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function getNonce(address target) external view returns (uint64 nonce);
    function addr(uint256 privateKey) external returns (address keyAddr);
    function sign(uint256 privateKey, bytes32 digest) external returns (uint8 v, bytes32 r, bytes32 s);
    function prank(address caller) external;
    function startPrank(address caller) external;
    function stopPrank() external;
    function roll(uint256 newHeight) external;
    function warp(uint256 newTimestamp) external;
    function snapshotState() external returns (uint256 snapshotId);
    function revertToState(uint256 snapshotId) external returns (bool ok);
    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory logs);
}

contract ReplayWorker {
    event Seen(address indexed caller, uint256 indexed value, uint256 balance);

    function who() external view returns (address) {
        return msg.sender;
    }

    function emitSeen(uint256 value) external {
        emit Seen(msg.sender, value, address(this).balance);
    }
}

contract LeanReplayCheatcodesTest {
    ReplayVm internal constant vm = ReplayVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant WORKER = 0x4000000000000000000000000000000000000004;
    address internal constant ALICE = 0xa11ce00000000000000000000000000000000001;
    address internal constant BOB = 0xb0b0000000000000000000000000000000000002;

    event LocalSeen(uint256 indexed value);

    function testLeanReplayStatefulCheatcodes() public {
        vm.etch(WORKER, type(ReplayWorker).runtimeCode);
        require(vm.getNonce(WORKER) == 0, "nonce");

        vm.deal(WORKER, 99);
        require(WORKER.balance == 99, "deal");

        address owner = vm.addr(0xBEEF);
        require(owner == 0x6E9972213BF459853FA33E28Ab7219e9157C8d02, "addr");
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(0xBEEF, 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef);
        require(v == 28, "sign v");
        require(r == 0x7a47531ffc70bcd501d967ec6e7fa72d2237a87ba8e6ed39d7d3bcae758b5208, "sign r");
        require(s == 0x5febc0e31fc8277e6dccabc7e352f5f3d74cf9430e8f56f04046072df586ecf8, "sign s");

        vm.prank(ALICE);
        require(ReplayWorker(WORKER).who() == ALICE, "one-shot prank");
        require(ReplayWorker(WORKER).who() == address(this), "prank reset");

        vm.startPrank(BOB);
        require(ReplayWorker(WORKER).who() == BOB, "start prank first");
        require(ReplayWorker(WORKER).who() == BOB, "start prank second");
        vm.stopPrank();
        require(ReplayWorker(WORKER).who() == address(this), "stop prank");

        vm.roll(12345);
        vm.warp(67890);
        require(block.number == 12345, "roll");
        require(block.timestamp == 67890, "warp");

        uint256 snapshot = vm.snapshotState();
        vm.deal(WORKER, 777);
        require(WORKER.balance == 777, "pre-revert deal");
        require(vm.revertToState(snapshot), "revert snapshot");
        require(WORKER.balance == 99, "snapshot balance");

        vm.recordLogs();
        ReplayWorker(WORKER).emitSeen(7);
        emit LocalSeen(8);
        ReplayVm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 2, "log length");
        require(logs[0].emitter == WORKER, "worker emitter");
        require(logs[0].topics.length == 3, "worker topic length");
        require(logs[0].topics[1] == bytes32(uint256(uint160(address(this)))), "worker caller topic");
        require(logs[0].topics[2] == bytes32(uint256(7)), "worker value topic");
        require(logs[1].emitter == address(this), "local emitter");
        require(logs[1].topics.length == 2, "local topic length");
        require(logs[1].topics[1] == bytes32(uint256(8)), "local value topic");
    }
}
