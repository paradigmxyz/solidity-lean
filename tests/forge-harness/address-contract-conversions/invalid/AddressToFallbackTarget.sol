// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FallbackTarget {
    fallback() external payable {}
}

contract AddressToFallbackTarget {
    function convert(address input) external pure returns (FallbackTarget) {
        return FallbackTarget(input);
    }
}
