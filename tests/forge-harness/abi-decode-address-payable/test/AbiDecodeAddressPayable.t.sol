// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {AbiDecodeAddressPayableHarnessTarget} from "../src/AbiDecodeAddressPayable.sol";

contract AbiDecodeAddressPayableForgeTest {
    function testPayableRoundtrip() public {
        AbiDecodeAddressPayableHarnessTarget t = new AbiDecodeAddressPayableHarnessTarget();
        address p = t.payableRoundtrip();
        require(p == address(uint160(0x1234)), "roundtrip");
    }

    function testSendToDecoded() public {
        AbiDecodeAddressPayableHarnessTarget t = new AbiDecodeAddressPayableHarnessTarget();
        bool ok = t.sendToDecoded();
        require(ok, "send");
    }
}
