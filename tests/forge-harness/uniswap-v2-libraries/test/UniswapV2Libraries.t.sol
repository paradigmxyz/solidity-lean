// SPDX-License-Identifier: GPL-3.0-only
pragma solidity ^0.8.20;

import {UniswapV2LibrariesHarness} from "../src/UniswapV2Libraries.sol";

contract UniswapV2LibrariesForgeTest {
    function testSortPairForAndPricing() public {
        UniswapV2LibrariesHarness target = new UniswapV2LibrariesHarness();

        address factory = address(0x1234567890123456789012345678901234567890);
        address tokenA = address(0x00000000000000000000000000000000000000AA);
        address tokenB = address(0x00000000000000000000000000000000000000bb);

        (address token0, address token1) = target.sort(tokenB, tokenA);
        require(token0 == tokenA, "token0");
        require(token1 == tokenB, "token1");

        bytes32 salt = keccak256(abi.encodePacked(tokenA, tokenB));
        address expected = address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(
                            hex"ff",
                            factory,
                            salt,
                            hex"96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f"
                        )
                    )
                )
            )
        );
        require(target.pairFor(factory, tokenB, tokenA) == expected, "pair");

        require(target.quote(3, 9, 12) == 4, "quote");
        require(target.amountOut(1000, 5000, 10000) == 1662, "amount out");
        require(target.amountIn(1662, 5000, 10000) == 1000, "amount in");
    }

    function testMathAndFixedPoint() public {
        UniswapV2LibrariesHarness target = new UniswapV2LibrariesHarness();

        require(target.min(17, 5) == 5, "min");
        require(target.sqrt(0) == 0, "sqrt zero");
        require(target.sqrt(1) == 1, "sqrt one");
        require(target.sqrt(4) == 2, "sqrt four");
        require(target.sqrt(9999) == 99, "sqrt floor");

        uint224 encoded = target.encode(5);
        require(encoded == uint224(5) * uint224(2 ** 112), "encode");
        require(target.uqdiv(encoded, 2) == encoded / 2, "uqdiv");
    }

    function testSafeMathAndReverts() public {
        UniswapV2LibrariesHarness target = new UniswapV2LibrariesHarness();

        require(target.safeAdd(40, 2) == 42, "add");
        require(target.safeSub(40, 2) == 38, "sub");
        require(target.safeMul(7, 6) == 42, "mul");

        try target.sort(address(0x11), address(0x11)) returns (
            address,
            address
        ) {
            revert("expected identical revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("UniswapV2Library: IDENTICAL_ADDRESSES")),
                "identical reason"
            );
        }

        try target.sort(address(0), address(0x11)) returns (address, address) {
            revert("expected zero revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("UniswapV2Library: ZERO_ADDRESS")),
                "zero reason"
            );
        }

        try target.quote(0, 9, 12) returns (uint256) {
            revert("expected amount revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("UniswapV2Library: INSUFFICIENT_AMOUNT")),
                "amount reason"
            );
        }

        try target.amountOut(1, 0, 12) returns (uint256) {
            revert("expected liquidity revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(
                        bytes("UniswapV2Library: INSUFFICIENT_LIQUIDITY")
                    ),
                "liquidity reason"
            );
        }

        try target.safeSub(1, 2) returns (uint256) {
            revert("expected sub revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ds-math-sub-underflow")),
                "sub reason"
            );
        }
    }
}
