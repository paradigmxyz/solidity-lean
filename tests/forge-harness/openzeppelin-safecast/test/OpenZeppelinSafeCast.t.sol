// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinSafeCast,
    OpenZeppelinSafeCastHarness
} from "../src/OpenZeppelinSafeCast.sol";

contract OpenZeppelinSafeCastForgeTest {
    function testUintDowncastsAndNamedReturn() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();

        require(target.castUint8(255) == 255, "uint8 max");
        require(target.castUint16(65535) == 65535, "uint16 max");
        require(target.namedDowncast(7) == 7, "named uint8");
    }

    function testSignedConversions() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();

        require(target.castUintFromInt(42) == 42, "int to uint");
        require(target.castInt8(127) == 127, "int8 max");
        require(target.castInt8(-128) == -128, "int8 min");
        require(
            target.castInt128(type(int128).max) == type(int128).max,
            "int128 max"
        );
        require(
            target.castInt128(type(int128).min) == type(int128).min,
            "int128 min"
        );
        require(
            target.castIntFromUint(uint256(type(int256).max)) ==
                type(int256).max,
            "uint to int"
        );
    }

    function testUintDowncastOverflowReverts() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();

        try target.castUint8(256) returns (uint256) {
            revert("expected uint8 overflow");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinSafeCast
                                .SafeCastOverflowedUintDowncast
                                .selector,
                            8,
                            256
                        )
                    ),
                "uint8 overflow reason"
            );
        }
    }

    function testIntToUintNegativeReverts() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();

        try target.castUintFromInt(-1) returns (uint256) {
            revert("expected negative overflow");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinSafeCast
                                .SafeCastOverflowedIntToUint
                                .selector,
                            -1
                        )
                    ),
                "negative reason"
            );
        }
    }

    function testIntDowncastOverflowReverts() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();

        try target.castInt8(128) returns (int256) {
            revert("expected int8 high overflow");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinSafeCast
                                .SafeCastOverflowedIntDowncast
                                .selector,
                            8,
                            128
                        )
                    ),
                "int8 high reason"
            );
        }

        try target.castInt8(-129) returns (int256) {
            revert("expected int8 low overflow");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinSafeCast
                                .SafeCastOverflowedIntDowncast
                                .selector,
                            8,
                            -129
                        )
                    ),
                "int8 low reason"
            );
        }
    }

    function testUintToIntOverflowReverts() public {
        OpenZeppelinSafeCastHarness target = new OpenZeppelinSafeCastHarness();
        uint256 tooLarge = uint256(type(int256).max) + 1;

        try target.castIntFromUint(tooLarge) returns (int256) {
            revert("expected uint to int overflow");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinSafeCast
                                .SafeCastOverflowedUintToInt
                                .selector,
                            tooLarge
                        )
                    ),
                "uint to int reason"
            );
        }
    }
}
