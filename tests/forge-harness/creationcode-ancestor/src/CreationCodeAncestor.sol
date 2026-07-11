// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract CreationCodeAncestorBase {}

contract CreationCodeAncestorTarget is CreationCodeAncestorBase {
    // `type(Base).creationCode` / `runtimeCode` for an ANCESTOR is a normal
    // acyclic bytecode dependency: solc accepts it (both are pure). Only a
    // genuine cycle (the contract's OWN code) is a "Circular reference" error.
    function ancestorCreation() public pure returns (bytes memory) {
        return type(CreationCodeAncestorBase).creationCode;
    }
    function ancestorRuntime() public pure returns (bytes memory) {
        return type(CreationCodeAncestorBase).runtimeCode;
    }
}
