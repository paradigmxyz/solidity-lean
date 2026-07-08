// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {GasHider} from "../src/GasHider.sol";

contract GasHiderForgeTest {
    GasHider private target = new GasHider();

    // Real on solc+EVM: gasleft() is a positive quantity. (The claim is real,
    // so the pipeline reaches the reject gate, which rejects it as OOS.)
    function testGasleftIsPositive() public view {
        require(target.entry() > 0, "gasleft should be positive");
    }
}
