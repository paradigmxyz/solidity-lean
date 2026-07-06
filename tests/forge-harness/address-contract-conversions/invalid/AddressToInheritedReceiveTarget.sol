// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReceiveBase {
    receive() external payable {}
}

contract InheritedTarget is ReceiveBase {}

contract AddressToInheritedReceiveTarget {
    function convert(address input) external pure returns (InheritedTarget) {
        return InheritedTarget(input);
    }
}
