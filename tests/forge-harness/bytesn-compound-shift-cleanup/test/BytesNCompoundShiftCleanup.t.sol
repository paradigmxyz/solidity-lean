// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {BytesNCompoundShiftCleanupTarget} from "../src/BytesNCompoundShiftCleanup.sol";

contract BytesNCompoundShiftCleanupTest {
    function fresh() internal returns (BytesNCompoundShiftCleanupTarget) {
        return new BytesNCompoundShiftCleanupTarget();
    }

    function testLocalShiftMasksWidth() public {
        require(fresh().localShift() == 0x22334400, "local left shift");
    }

    function testMappingShiftMasksWidth() public {
        require(fresh().mappingShift() == 0x22334400, "mapping left shift");
    }

    function testStateShiftRemainsCorrect() public {
        require(fresh().stateShift() == 0x22334400, "state left shift");
    }

    function testArrayShiftRemainsCorrect() public {
        require(fresh().arrayShift() == 0x22334400, "array left shift");
    }

    function testRightShiftRemainsCorrect() public {
        require(fresh().rightShift() == 0x00112233, "right shift");
    }
}
