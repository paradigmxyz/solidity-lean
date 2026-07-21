// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageArrayLiteralHarnessTarget} from "../src/StorageArrayLiteral.sol";

interface Vm {
    function expectEmit(bool, bool, bool, bool) external;
}

contract StorageArrayLiteralForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    StorageArrayLiteralHarnessTarget private t =
        new StorageArrayLiteralHarnessTarget();

    event EBytes(bytes[2] arr);
    error EArr(bytes[2] arr);

    function testEncBytes() public {
        require(t.encBytes() == 224 * 1000000 + 0xaa * 1000 + 0xbb,
            "encBytes");
    }

    function testEncStrings() public {
        require(t.encStrings() == 224 * 1000000 + 104 * 1000 + 121,
            "encStrings");
    }

    function testEncPointers() public {
        require(t.encPointers() == 224 * 1000000 + 0xaa * 1000 + 0xbb,
            "encPointers");
    }

    function testHashMatches() public {
        require(t.hashMatches() == 1, "hashMatches");
    }

    function testEncArrays() public {
        require(t.encArrays() == 288 * 1000000 + 7 * 1000 + 2, "encArrays");
    }

    function testEncTernaryTrue() public {
        require(t.encTernary(true) == 224 * 1000000 + 0xaa * 1000 + 0xbb,
            "encTernary(true)");
    }

    function testEncTernaryFalse() public {
        require(t.encTernary(false) == 224 * 1000000 + 0xbb * 1000 + 0xbb,
            "encTernary(false)");
    }

    function testEmitBytes() public {
        bytes[2] memory expected;
        expected[0] = hex"aa";
        expected[1] = hex"bbcc";
        vm.expectEmit(false, false, false, true);
        emit EBytes(expected);
        require(t.emitBytes() == 1, "emitBytes");
    }

    function testEncLocals() public view {
        require(t.encLocals(7, 9) == 64 * 1000 + 9, "encLocals");
    }

    function testRevertArr() public {
        bytes[2] memory expected;
        expected[0] = hex"aa";
        expected[1] = hex"bbcc";
        (bool ok, bytes memory data) = address(t).call(
            abi.encodeWithSignature("revertArr()"));
        require(!ok, "revertArr must revert");
        require(keccak256(data) ==
            keccak256(abi.encodeWithSelector(EArr.selector, expected)),
            "revertArr data");
    }
}
