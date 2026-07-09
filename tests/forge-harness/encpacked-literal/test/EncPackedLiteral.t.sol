// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EncPackedLiteral} from "../src/EncPackedLiteral.sol";

contract EncPackedLiteralForgeTest {
    EncPackedLiteral private target = new EncPackedLiteral();

    function testPackLiteralsOnly() public view {
        // uint8(1)=01, true=01, "ab"=6162, hex"cd"=cd
        require(
            keccak256(target.packLiteralsOnly()) == keccak256(hex"01016162cd"),
            "packLiteralsOnly bytes mismatch"
        );
    }

    function testPackAll() public view {
        bytes memory packed = target.packAll(0x1234, address(0xABcD));
        // uint8(1)=1, true=1, "ab"=2, hex"cd"=1, x(uint16)=2, a(address)=20,
        // e=E.B=1 byte
        require(packed.length == 1 + 1 + 2 + 1 + 2 + 20 + 1, "packAll length");
    }
}
