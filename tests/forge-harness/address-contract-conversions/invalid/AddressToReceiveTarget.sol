// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReceiveTarget {
    receive() external payable {}
}

contract AddressToReceiveTarget {
    function convert(address input) external pure returns (ReceiveTarget) {
        return ReceiveTarget(input);
    }
}
