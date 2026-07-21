// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageReturnSubfieldOpsHarnessTarget} from "../src/StorageReturnSubfieldOps.sol";

contract StorageReturnSubfieldOpsForgeTest {
    function fresh() internal returns (StorageReturnSubfieldOpsHarnessTarget) {
        return new StorageReturnSubfieldOpsHarnessTarget();
    }

    function testMapShapes() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.mapWhole(3, 44) == 44, "map whole");
        require(h.mapMember(3, 45) == 45, "map member");
        require(h.mapPick(3, 46, true) == 46, "map pick true");
        require(h.mapPick(4, 47, false) == 47, "map pick false");
    }

    function testPushShapes() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.pushWhole(47) == 47, "push whole");
        require(h.pushMember(48) == 48, "push member");
        require(h.pushLocal(49) == 49, "push local");
    }

    function testPushEmptyThenWrite() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.pushEmptyThenWrite(50) == 50, "push() then write");
    }

    function testPushPushPop() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.pushPushPop(51) == 1051, "push push pop => len 1, a[0] 51");
    }

    function testPushNarrowFits() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.pushNarrow(200, 55) == 255, "narrow push fits");
    }

    function testPushNarrowOverflowPanics() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        (bool ok, bytes memory data) = address(h).call(
            abi.encodeWithSignature("pushNarrow(uint8,uint8)", uint8(200), uint8(56)));
        require(!ok, "must revert");
        require(data.length == 36, "panic payload");
        require(bytes4(data) == 0x4e487b71, "Panic selector");
        uint256 code;
        assembly { code := mload(add(data, 36)) }
        require(code == 0x11, "Panic 0x11");
    }

    function testFieldAndLen() public {
        StorageReturnSubfieldOpsHarnessTarget h = fresh();
        require(h.fieldPick(52, true) == 52, "field pick true");
        require(h.fieldPick(53, false) == 53, "field pick false");
        require(h.lenAfterPush(1) == 2, "len after two pushes");
    }
}
