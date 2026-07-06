// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Import-free adaptation of selected functions from OpenZeppelin Contracts
// v5.6.1 `utils/math/SafeCast.sol`.
library OpenZeppelinSafeCast {
    error SafeCastOverflowedUintDowncast(uint8 bits, uint256 value);
    error SafeCastOverflowedIntToUint(int256 value);
    error SafeCastOverflowedIntDowncast(uint8 bits, int256 value);
    error SafeCastOverflowedUintToInt(uint256 value);

    function toUint16(uint256 value) internal pure returns (uint16) {
        if (value > type(uint16).max) {
            revert SafeCastOverflowedUintDowncast(16, value);
        }
        return uint16(value);
    }

    function toUint8(uint256 value) internal pure returns (uint8) {
        if (value > type(uint8).max) {
            revert SafeCastOverflowedUintDowncast(8, value);
        }
        return uint8(value);
    }

    function toUint256(int256 value) internal pure returns (uint256) {
        if (value < 0) {
            revert SafeCastOverflowedIntToUint(value);
        }
        return uint256(value);
    }

    function toInt128(int256 value) internal pure returns (int128 downcasted) {
        downcasted = int128(value);
        if (downcasted != value) {
            revert SafeCastOverflowedIntDowncast(128, value);
        }
    }

    function toInt8(int256 value) internal pure returns (int8 downcasted) {
        downcasted = int8(value);
        if (downcasted != value) {
            revert SafeCastOverflowedIntDowncast(8, value);
        }
    }

    function toInt256(uint256 value) internal pure returns (int256) {
        if (value > uint256(type(int256).max)) {
            revert SafeCastOverflowedUintToInt(value);
        }
        return int256(value);
    }
}

contract OpenZeppelinSafeCastHarness {
    function castUint8(uint256 value) external pure returns (uint256) {
        return OpenZeppelinSafeCast.toUint8(value);
    }

    function castUint16(uint256 value) external pure returns (uint256) {
        return OpenZeppelinSafeCast.toUint16(value);
    }

    function castUintFromInt(int256 value) external pure returns (uint256) {
        return OpenZeppelinSafeCast.toUint256(value);
    }

    function castInt8(int256 value) external pure returns (int256) {
        return OpenZeppelinSafeCast.toInt8(value);
    }

    function castInt128(int256 value) external pure returns (int256) {
        return OpenZeppelinSafeCast.toInt128(value);
    }

    function castIntFromUint(uint256 value) external pure returns (int256) {
        return OpenZeppelinSafeCast.toInt256(value);
    }

    function namedDowncast(uint256 value)
        external
        pure
        returns (uint8 downcasted)
    {
        downcasted = OpenZeppelinSafeCast.toUint8(value);
    }
}
