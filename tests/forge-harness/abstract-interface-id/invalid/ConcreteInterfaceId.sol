// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A concrete, deployable contract has NO `.interfaceId` member — solc rejects
// `type(Deployable).interfaceId` (Types.cpp:4271-4285: member exposed only when
// `!canBeDeployed()`). This pins the concrete-contract reject that the fix must
// preserve.
contract Deployable {
    function ping() external pure returns (uint256) {
        return 1;
    }
}

contract ConcreteInterfaceId {
    function bad() external pure returns (bytes4) {
        return type(Deployable).interfaceId;
    }
}
