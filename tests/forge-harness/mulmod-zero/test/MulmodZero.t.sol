// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {MulmodZeroHarnessTarget} from "../src/MulmodZero.sol";

// Pins solc/EVM behavior of the MULMOD0 accepted controls: a runtime (non
// constant) zero modulus is a Panic 0x12 at runtime (NOT a compile error), and
// a constant non-zero modulus folds to solc's value.
contract MulmodZeroForgeTest {
    MulmodZeroHarnessTarget private target = new MulmodZeroHarnessTarget();

    // Panic(uint256) selector, code 0x12 (division or modulo by zero).
    function _assertPanic0x12(bytes memory data) private pure {
        require(data.length == 36, "panic length");
        bytes4 selector =
            bytes4(data[0]) | (bytes4(data[1]) >> 8) |
            (bytes4(data[2]) >> 16) | (bytes4(data[3]) >> 24);
        require(selector == bytes4(0x4e487b71), "panic selector");
        uint256 code;
        assembly {
            code := mload(add(data, 0x24))
        }
        require(code == 0x12, "panic code 0x12");
    }

    function testRuntimeZeroModulusMulPanics() public view {
        (bool ok, bytes memory data) = address(target).staticcall(
            abi.encodeWithSignature("runtimeMulmod(uint256)", uint256(0)));
        require(!ok, "runtimeMulmod(0) should revert");
        _assertPanic0x12(data);
    }

    function testRuntimeZeroModulusAddPanics() public view {
        (bool ok, bytes memory data) = address(target).staticcall(
            abi.encodeWithSignature("runtimeAddmod(uint256)", uint256(0)));
        require(!ok, "runtimeAddmod(0) should revert");
        _assertPanic0x12(data);
    }

    function testRuntimeNonzeroModulusFolds() public view {
        require(target.runtimeMulmod(7) == 6, "mulmod(2,3,7)=6");
        require(target.runtimeAddmod(7) == 5, "addmod(2,3,7)=5");
    }

    function testConstantNonzeroModulusFolds() public view {
        require(target.constNonzeroMul() == 6, "const mulmod(2,3,7)=6");
        require(target.constNonzeroAdd() == 5, "const addmod(2,3,7)=5");
    }
}
