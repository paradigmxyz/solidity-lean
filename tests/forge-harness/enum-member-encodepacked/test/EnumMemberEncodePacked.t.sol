// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EnumMemberEncodePacked} from "../src/EnumMemberEncodePacked.sol";

contract EnumMemberEncodePackedForgeTest {
    EnumMemberEncodePacked private target = new EnumMemberEncodePacked();

    function testPackMember() public view {
        bytes memory packed = target.packMember();
        require(packed.length == 1, "packMember length");
        require(keccak256(packed) == keccak256(hex"02"), "packMember bytes");
    }

    function testPackMixed() public view {
        bytes memory packed = target.packMixed();
        require(packed.length == 3, "packMixed length");
        require(keccak256(packed) == keccak256(hex"010209"), "packMixed bytes");
    }

    function testConstFold() public view {
        require(target.constFold() == 2, "constFold value");
    }
}
