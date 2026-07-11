// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CreationCodeAncestorTarget} from "../src/CreationCodeAncestor.sol";

contract CreationCodeAncestorForgeTest {
    function testAncestorCreationCodeNonEmpty() public {
        CreationCodeAncestorTarget t = new CreationCodeAncestorTarget();
        require(t.ancestorCreation().length > 0, "creation empty");
    }
    function testAncestorRuntimeCodeNonEmpty() public {
        CreationCodeAncestorTarget t = new CreationCodeAncestorTarget();
        require(t.ancestorRuntime().length > 0, "runtime empty");
    }
}
