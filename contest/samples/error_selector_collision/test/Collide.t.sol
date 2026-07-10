// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Entry} from "../src/Collide.sol";
contract CollideForgeTest {
    Entry private target = new Entry();
    function testReverts() public {
        (bool ok, bytes memory ret) = address(target).call(abi.encodeWithSignature("f()"));
        require(!ok, "f() should revert");
        // revert data is exactly the 4-byte selector 0x554d5780, no args.
        require(ret.length == 4, "selector-only revert");
    }
}
