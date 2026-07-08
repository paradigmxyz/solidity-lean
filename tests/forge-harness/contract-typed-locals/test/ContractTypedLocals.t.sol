// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ContractTypedLocals} from "../src/ContractTypedLocals.sol";

contract ContractTypedLocalsForgeTest {
    ContractTypedLocals private target = new ContractTypedLocals();

    function testContractLocalPreservesAddress() public view {
        require(
            target.addrOfContract() == 0x1234567890abcdef1234,
            "Other(literal)->address"
        );
    }

    function testContractLocalRoundTrip() public view {
        address a = address(uint160(0xdeadbeef00112233));
        require(target.roundTrip(a) == a, "address->Other->address");
        require(
            target.passAsAddress(a) == uint160(a),
            "contract local as address arg"
        );
    }

    function testContractLocalBalance() public view {
        // an unfunded address: 0 balance in the Foundry EVM and the empty state
        require(
            target.balanceOfLocal(address(uint160(0x9999))) == 0,
            "local .balance"
        );
    }
}
