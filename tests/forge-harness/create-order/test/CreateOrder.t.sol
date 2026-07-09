// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {CreateOrder} from "../src/CreateOrder.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for contract-creation option/
/// argument evaluation order (gaps DIV-CREATE-1/2): the `{...}` options in
/// written order FIRST, then the constructor argument LAST, yielding
/// order-trace 123 for `{value, salt}` and 213 for `{salt, value}`, identically
/// for the plain `new` expression and the statement-form `try new`.
contract CreateOrderForgeTest {
    function testPlainValueFirst() public {
        CreateOrder c = new CreateOrder();
        require(c.plainValueFirst() == 123, "plain {value,salt}");
    }

    function testPlainSaltFirst() public {
        CreateOrder c = new CreateOrder();
        require(c.plainSaltFirst() == 213, "plain {salt,value}");
    }

    function testTryValueFirst() public {
        CreateOrder c = new CreateOrder();
        require(c.tryValueFirst() == 123, "try {value,salt}");
    }

    function testTrySaltFirst() public {
        CreateOrder c = new CreateOrder();
        require(c.trySaltFirst() == 213, "try {salt,value}");
    }
}
