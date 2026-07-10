// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    LitCoercionFamily,
    LitPtrTarget,
    LitPtrCaller
} from "../src/LitCoercionFamily.sol";

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;
    function getRecordedLogs() external returns (Log[] memory entries);
}

contract LitCoercionFamilyForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    LitCoercionFamily internal fam;

    error Bad(bytes2 x);

    function setUp() public {
        fam = new LitCoercionFamily();
    }

    // #141 emit non-indexed: data word is the left-aligned literal.
    function testEmitData() public {
        vm.recordLogs();
        fam.emitData();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics[0] == keccak256("EvData(bytes2)"), "topic0");
        require(
            keccak256(logs[0].data) ==
                keccak256(
                    hex"1234000000000000000000000000000000000000000000000000000000000000"
                ),
            "data word"
        );
    }

    // #141 emit indexed: bytesN indexed topic is the left-aligned word (unhashed).
    function testEmitIdx() public {
        vm.recordLogs();
        fam.emitIdx();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics.length == 2, "two topics");
        require(logs[0].topics[0] == keccak256("EvIdx(bytes2)"), "topic0");
        require(
            logs[0].topics[1] ==
                bytes32(
                    hex"1234000000000000000000000000000000000000000000000000000000000000"
                ),
            "topic1 word"
        );
        require(logs[0].data.length == 0, "no data");
    }

    // #141 revert: encoded custom-error data is selector + one left-aligned word.
    function testDoRevert() public {
        (bool ok, bytes memory ret) =
            address(fam).staticcall(abi.encodeWithSignature("doRevert()"));
        require(!ok, "reverts");
        require(
            keccak256(ret) ==
                keccak256(
                    abi.encodePacked(
                        Bad.selector,
                        hex"1234000000000000000000000000000000000000000000000000000000000000"
                    )
                ),
            "revert data"
        );
    }

    // #141 require with custom error: same encoded data.
    function testDoRequire() public {
        (bool ok, bytes memory ret) =
            address(fam).staticcall(abi.encodeWithSignature("doRequire()"));
        require(!ok, "reverts");
        require(
            keccak256(ret) ==
                keccak256(
                    abi.encodePacked(
                        Bad.selector,
                        hex"1234000000000000000000000000000000000000000000000000000000000000"
                    )
                ),
            "require data"
        );
    }

    // #142 push: pushed bytes2 element reads back as 0x1234.
    function testPushLit() public {
        fam.pushLit();
        require(fam.arr(0) == bytes2(hex"1234"), "arr[0]");
    }

    // #145 mapping key: string literal key stores/reads at the same slot.
    function testSetMap() public {
        fam.setMap();
        require(fam.m("abcd") == 7, "m[abcd]");
        require(fam.m(bytes4(hex"61626364")) == 7, "m[0x61626364]");
    }

    // #143 encodeWithSelector: bare 4-byte hex selector accepted.
    function testSelData() public view {
        bytes memory got = fam.selData();
        require(
            keccak256(got) ==
                keccak256(abi.encodeWithSelector(bytes4(0x12345678), uint256(7))),
            "sel data"
        );
    }

    // #144 external function-pointer value call: literal arg is left-aligned word.
    function testCallPtr() public {
        LitPtrTarget target = new LitPtrTarget();
        LitPtrCaller caller = new LitPtrCaller();
        require(caller.callPtr(address(target)) == bytes4("abcd"), "ptr call");
    }

    // CONTROL: dynamic bytes event field stays dynamic (offset/length/data).
    function testEmitDynStaysDynamic() public {
        vm.recordLogs();
        fam.emitDyn();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(
            keccak256(logs[0].data) == keccak256(abi.encode(bytes(hex"1234"))),
            "dynamic data"
        );
        require(logs[0].data.length == 96, "dyn length");
    }

    // CONTROL: non-literal bytes2 variable arg == the coerced literal.
    function testEmitVarUnchanged() public {
        vm.recordLogs();
        fam.emitVar(bytes2(hex"1234"));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(
            keccak256(logs[0].data) ==
                keccak256(
                    hex"1234000000000000000000000000000000000000000000000000000000000000"
                ),
            "var data word"
        );
    }
}
