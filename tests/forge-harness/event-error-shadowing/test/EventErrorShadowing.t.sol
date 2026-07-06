// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {
    InheritedDerived,
    LocalShadow,
    UsesFreeEventError
} from "../src/EventErrorShadowing.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract EventErrorShadowingForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    UsesFreeEventError private freeTarget = new UsesFreeEventError();
    LocalShadow private localTarget = new LocalShadow();
    InheritedDerived private inheritedTarget = new InheritedDerived();

    function testFreeEventNamedArguments() public {
        vm.recordLogs();
        freeTarget.emitFreeNamed(4);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(freeTarget), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("FileHit(uint256,uint256)"),
            "topic0"
        );
        require(entries[0].topics[1] == bytes32(uint256(4)), "topic1");
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(uint256(6))),
            "data"
        );
    }

    function testLocalEventShadow() public {
        address who = address(0xBEEF);

        vm.recordLogs();
        localTarget.emitLocal(who, 7);
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(localTarget), "emitter");
        require(entries[0].topics.length == 2, "topic count");
        require(
            entries[0].topics[0] == keccak256("FileHit(address,uint256)"),
            "topic0"
        );
        require(
            entries[0].topics[1] == bytes32(uint256(uint160(who))),
            "topic1"
        );
        require(
            keccak256(entries[0].data) == keccak256(abi.encode(uint256(7))),
            "data"
        );
    }

    function testInheritedEventShadow() public {
        vm.recordLogs();
        inheritedTarget.emitInherited();
        Vm.Log[] memory entries = vm.getRecordedLogs();

        require(entries.length == 1, "log count");
        require(entries[0].emitter == address(inheritedTarget), "emitter");
        require(entries[0].topics.length == 1, "topic count");
        require(
            entries[0].topics[0] == keccak256("CollisionEvent()"),
            "topic0"
        );
        require(entries[0].data.length == 0, "data");
    }

    function testFreeErrorSelector() public {
        try freeTarget.failFree(4) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                bytes4(keccak256("FileBad(uint256)")),
                uint256(4)
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }

    function testLocalErrorShadow() public {
        address who = address(0xBEEF);

        try localTarget.failLocal(who) {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                bytes4(keccak256("FileBad(address)")),
                who
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }

    function testInheritedErrorShadow() public {
        try inheritedTarget.failInherited() {
            revert("expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSelector(
                bytes4(keccak256("Collision()"))
            );
            require(keccak256(data) == keccak256(expected), "data");
        }
    }
}
