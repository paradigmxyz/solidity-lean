// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract AbstractFallbackWithoutVirtual {
    fallback() external;
}
