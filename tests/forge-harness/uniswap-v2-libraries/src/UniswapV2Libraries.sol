// SPDX-License-Identifier: GPL-3.0-only
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of Uniswap V2 periphery/core
// libraries: SafeMath, UniswapV2Library pure functions, Math, and UQ112x112.
library UniswapV2SafeMath {
    function add(uint256 x, uint256 y) internal pure returns (uint256 z) {
        unchecked {
            z = x + y;
        }
        require(z >= x, "ds-math-add-overflow");
    }

    function sub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        unchecked {
            z = x - y;
        }
        require(z <= x, "ds-math-sub-underflow");
    }

    function mul(uint256 x, uint256 y) internal pure returns (uint256 z) {
        unchecked {
            z = x * y;
        }
        require(y == 0 || z / y == x, "ds-math-mul-overflow");
    }
}

library UniswapV2Math {
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        z = x < y ? x : y;
    }

    function sqrt(uint256 y) internal pure returns (uint256 z) {
        if (y > 3) {
            z = y;
            uint256 x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }
}

library UniswapV2UQ112x112 {
    uint224 internal constant Q112 = 2 ** 112;

    function encode(uint112 y) internal pure returns (uint224 z) {
        z = uint224(y) * Q112;
    }

    function uqdiv(uint224 x, uint112 y) internal pure returns (uint224 z) {
        z = x / uint224(y);
    }
}

library UniswapV2Library {
    using UniswapV2SafeMath for uint256;

    function sortTokens(address tokenA, address tokenB)
        internal
        pure
        returns (address token0, address token1)
    {
        require(
            tokenA != tokenB,
            "UniswapV2Library: IDENTICAL_ADDRESSES"
        );
        (token0, token1) = tokenA < tokenB
            ? (tokenA, tokenB)
            : (tokenB, tokenA);
        require(token0 != address(0), "UniswapV2Library: ZERO_ADDRESS");
    }

    function pairFor(address factory, address tokenA, address tokenB)
        internal
        pure
        returns (address pair)
    {
        (address token0, address token1) = sortTokens(tokenA, tokenB);
        pair = address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(
                            hex"ff",
                            factory,
                            keccak256(abi.encodePacked(token0, token1)),
                            hex"96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f"
                        )
                    )
                )
            )
        );
    }

    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB)
        internal
        pure
        returns (uint256 amountB)
    {
        require(amountA > 0, "UniswapV2Library: INSUFFICIENT_AMOUNT");
        require(
            reserveA > 0 && reserveB > 0,
            "UniswapV2Library: INSUFFICIENT_LIQUIDITY"
        );
        amountB = amountA.mul(reserveB) / reserveA;
    }

    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountOut) {
        require(
            amountIn > 0,
            "UniswapV2Library: INSUFFICIENT_INPUT_AMOUNT"
        );
        require(
            reserveIn > 0 && reserveOut > 0,
            "UniswapV2Library: INSUFFICIENT_LIQUIDITY"
        );
        uint256 amountInWithFee = amountIn.mul(997);
        uint256 numerator = amountInWithFee.mul(reserveOut);
        uint256 denominator = reserveIn.mul(1000).add(amountInWithFee);
        amountOut = numerator / denominator;
    }

    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountIn) {
        require(
            amountOut > 0,
            "UniswapV2Library: INSUFFICIENT_OUTPUT_AMOUNT"
        );
        require(
            reserveIn > 0 && reserveOut > 0,
            "UniswapV2Library: INSUFFICIENT_LIQUIDITY"
        );
        uint256 numerator = reserveIn.mul(amountOut).mul(1000);
        uint256 denominator = reserveOut.sub(amountOut).mul(997);
        amountIn = (numerator / denominator).add(1);
    }
}

contract UniswapV2LibrariesHarness {
    function sort(address tokenA, address tokenB)
        external
        pure
        returns (address, address)
    {
        return UniswapV2Library.sortTokens(tokenA, tokenB);
    }

    function pairFor(address factory, address tokenA, address tokenB)
        external
        pure
        returns (address)
    {
        return UniswapV2Library.pairFor(factory, tokenA, tokenB);
    }

    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB)
        external
        pure
        returns (uint256)
    {
        return UniswapV2Library.quote(amountA, reserveA, reserveB);
    }

    function amountOut(
        uint256 inputAmount,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256) {
        return UniswapV2Library.getAmountOut(
            inputAmount,
            reserveIn,
            reserveOut
        );
    }

    function amountIn(
        uint256 outputAmount,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256) {
        return UniswapV2Library.getAmountIn(
            outputAmount,
            reserveIn,
            reserveOut
        );
    }

    function min(uint256 x, uint256 y) external pure returns (uint256) {
        return UniswapV2Math.min(x, y);
    }

    function sqrt(uint256 y) external pure returns (uint256) {
        return UniswapV2Math.sqrt(y);
    }

    function encode(uint112 y) external pure returns (uint224) {
        return UniswapV2UQ112x112.encode(y);
    }

    function uqdiv(uint224 x, uint112 y) external pure returns (uint224) {
        return UniswapV2UQ112x112.uqdiv(x, y);
    }

    function safeAdd(uint256 x, uint256 y) external pure returns (uint256) {
        return UniswapV2SafeMath.add(x, y);
    }

    function safeSub(uint256 x, uint256 y) external pure returns (uint256) {
        return UniswapV2SafeMath.sub(x, y);
    }

    function safeMul(uint256 x, uint256 y) external pure returns (uint256) {
        return UniswapV2SafeMath.mul(x, y);
    }
}
