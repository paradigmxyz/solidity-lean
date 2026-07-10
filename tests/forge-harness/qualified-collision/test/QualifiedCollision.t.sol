// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {QualifiedCollisionTarget} from "../src/QualifiedCollision.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract QualifiedCollisionForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    QualifiedCollisionTarget private target =
        new QualifiedCollisionTarget();

    function testEmitLibTopic() public {
        // Library-qualified emit under a name collision resolves to L.Ev(uint8).
        vm.recordLogs();
        target.emitLib();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "emitLib log count");
        require(logs[0].topics[0] == keccak256("Ev(uint8)"), "emitLib topic0");
    }

    function testEmitOwnTopic() public {
        // The contract's own bare event stays Ev(uint256).
        vm.recordLogs();
        target.emitOwn();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "emitOwn log count");
        require(logs[0].topics[0] == keccak256("Ev(uint256)"), "emitOwn topic0");
    }

    function testEmitLibNoCollisionTopic() public {
        vm.recordLogs();
        target.emitLibNoCollision();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "emitLibNoCollision log count");
        require(
            logs[0].topics[0] == keccak256("Ping(uint64)"),
            "emitLibNoCollision topic0"
        );
    }

    function testRevertLibSelector() public {
        // Library-qualified revert under a name collision resolves to L.E(uint8).
        try target.revertLib() {
            revert("expected revert");
        } catch (bytes memory data) {
            require(data.length >= 4, "revertLib short");
            require(bytes4(data) == bytes4(keccak256("E(uint8)")), "revertLib selector");
        }
    }

    function testRevertOwnSelector() public {
        try target.revertOwn() {
            revert("expected revert");
        } catch (bytes memory data) {
            require(data.length >= 4, "revertOwn short");
            require(bytes4(data) == bytes4(keccak256("E(uint256)")), "revertOwn selector");
        }
    }

    function testRevertLibNoCollisionSelector() public {
        try target.revertLibNoCollision() {
            revert("expected revert");
        } catch (bytes memory data) {
            require(data.length >= 4, "revertLibNoCollision short");
            require(
                bytes4(data) == bytes4(keccak256("Bad(uint64)")),
                "revertLibNoCollision selector"
            );
        }
    }
}
