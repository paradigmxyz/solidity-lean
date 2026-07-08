// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// C2: a deployable concrete contract has no `type(C).interfaceId`
// (Types.cpp:4271-4285 — only interface/abstract expose interfaceId).
contract C2Concrete {
    function foo() public {}
}

contract C2ConcreteReader {
    function f() public pure returns (bytes4) {
        return type(C2Concrete).interfaceId;
    }
}
