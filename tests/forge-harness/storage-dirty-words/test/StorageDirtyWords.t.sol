// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {StorageDirtyWordsHarnessTarget} from "../src/StorageDirtyWords.sol";

interface VmStore {
    function store(address target, bytes32 slot, bytes32 value) external;
}

contract StorageDirtyWordsForgeTest {
    VmStore internal constant vm =
        VmStore(address(uint160(uint256(keccak256("hevm cheat code")))));

    function newTarget() internal returns (StorageDirtyWordsHarnessTarget) {
        return new StorageDirtyWordsHarnessTarget();
    }

    function expectPanic21(address target, bytes memory callData)
        internal
        view
    {
        (bool ok, bytes memory data) = target.staticcall(callData);
        require(!ok, "expected revert");
        require(data.length == 36, "panic payload length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(data, 0x20))
            code := mload(add(data, 0x24))
        }
        require(selector == bytes4(0x4e487b71), "panic selector");
        require(code == 0x21, "panic code 0x21");
    }

    function testDirtyBoolReads() public {
        StorageDirtyWordsHarnessTarget target = newTarget();
        // Non-canonical truthy word: low byte 2 -> observably true.
        vm.store(address(target), bytes32(uint256(0)), bytes32(uint256(2)));
        require(target.flag(), "flag getter true on 2");
        require(target.flagIsTrue(), "flag use true on 2");
        // High garbage with zero low byte -> observably false.
        vm.store(
            address(target), bytes32(uint256(0)), bytes32(uint256(1) << 200)
        );
        require(!target.flag(), "flag getter false on high-bits word");
        require(!target.flagIsTrue(), "flag use false on high-bits word");
    }

    function testDirtyEnumReads() public {
        StorageDirtyWordsHarnessTarget target = newTarget();
        // Out-of-range member index: every use panics 0x21.
        vm.store(address(target), bytes32(uint256(2)), bytes32(uint256(7)));
        expectPanic21(
            address(target), abi.encodeWithSignature("choice()")
        );
        expectPanic21(
            address(target), abi.encodeWithSignature("choiceIsB()")
        );
        expectPanic21(
            address(target), abi.encodeWithSignature("choiceAsUint()")
        );
        // Dirty high bits are masked before the range check: in-range low
        // byte reads fine.
        vm.store(
            address(target),
            bytes32(uint256(2)),
            bytes32((uint256(1) << 200) | uint256(1))
        );
        require(
            target.choice() == StorageDirtyWordsHarnessTarget.DirtyChoice.B,
            "masked enum reads member B"
        );
        require(target.choiceIsB(), "masked enum compares equal to B");
        require(target.choiceAsUint() == 1, "masked enum converts to 1");
    }

    function testDirtyAddressRead() public {
        StorageDirtyWordsHarnessTarget target = newTarget();
        vm.store(
            address(target),
            bytes32(uint256(4)),
            bytes32((uint256(1) << 160) | uint256(0xabcd))
        );
        require(
            target.who() == address(uint160(0xabcd)),
            "address high bits dropped"
        );
    }

    function testDirtyFixedBytesRead() public {
        StorageDirtyWordsHarnessTarget target = newTarget();
        vm.store(
            address(target),
            bytes32(uint256(6)),
            bytes32((uint256(1) << 200) | uint256(0x11223344))
        );
        require(
            target.tag() == bytes4(0x11223344),
            "bytes4 bits above the lane dropped"
        );
    }

    function testDirtyPackedIntReads() public {
        StorageDirtyWordsHarnessTarget target = newTarget();
        // slot 8: u8v at byte 0 = 0xff, i8v at byte 1 = 0x80, garbage above.
        vm.store(
            address(target),
            bytes32(uint256(8)),
            bytes32((uint256(1) << 200) | uint256(0x80ff))
        );
        require(target.u8v() == 0xff, "u8 lane masked");
        require(target.i8v() == -128, "i8 lane sign-extended");
    }
}
