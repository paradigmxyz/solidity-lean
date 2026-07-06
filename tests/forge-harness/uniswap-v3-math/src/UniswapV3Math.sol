// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.20;

// Import-inlined, assembly-free adaptation of Uniswap V3 Core `BitMath.sol`
// and the `getSqrtRatioAtTick` half of `TickMath.sol`. The inverse
// `getTickAtSqrtRatio` function is intentionally omitted because upstream uses
// inline assembly/Yul, which is outside this source-semantics harness boundary.
library UniswapV3BitMath {
    function mostSignificantBit(uint256 x) internal pure returns (uint8 r) {
        require(x > 0);

        if (x >= 0x100000000000000000000000000000000) {
            x >>= 128;
            r += 128;
        }
        if (x >= 0x10000000000000000) {
            x >>= 64;
            r += 64;
        }
        if (x >= 0x100000000) {
            x >>= 32;
            r += 32;
        }
        if (x >= 0x10000) {
            x >>= 16;
            r += 16;
        }
        if (x >= 0x100) {
            x >>= 8;
            r += 8;
        }
        if (x >= 0x10) {
            x >>= 4;
            r += 4;
        }
        if (x >= 0x4) {
            x >>= 2;
            r += 2;
        }
        if (x >= 0x2) {
            r += 1;
        }
    }

    function leastSignificantBit(uint256 x) internal pure returns (uint8 r) {
        require(x > 0);

        r = 255;
        if (x & type(uint128).max > 0) {
            r -= 128;
        } else {
            x >>= 128;
        }
        if (x & type(uint64).max > 0) {
            r -= 64;
        } else {
            x >>= 64;
        }
        if (x & type(uint32).max > 0) {
            r -= 32;
        } else {
            x >>= 32;
        }
        if (x & type(uint16).max > 0) {
            r -= 16;
        } else {
            x >>= 16;
        }
        if (x & type(uint8).max > 0) {
            r -= 8;
        } else {
            x >>= 8;
        }
        if (x & 0xf > 0) {
            r -= 4;
        } else {
            x >>= 4;
        }
        if (x & 0x3 > 0) {
            r -= 2;
        } else {
            x >>= 2;
        }
        if (x & 0x1 > 0) {
            r -= 1;
        }
    }
}

library UniswapV3TickMath {
    int24 internal constant MIN_TICK = -887272;
    int24 internal constant MAX_TICK = -MIN_TICK;

    uint160 internal constant MIN_SQRT_RATIO = 4295128739;
    uint160 internal constant MAX_SQRT_RATIO =
        1461446703485210103287273052203988822378723970342;

    function getSqrtRatioAtTick(int24 tick)
        internal
        pure
        returns (uint160 sqrtPriceX96)
    {
        int256 tick256 = tick;
        uint256 absTick = tick < 0 ? uint256(-tick256) : uint256(tick256);
        require(absTick <= 887272, "T");

        unchecked {
            uint256 ratio = absTick & 0x1 != 0
                ? 0xfffcb933bd6fad37aa2d162d1a594001
                : 0x100000000000000000000000000000000;
            if (absTick & 0x2 != 0) {
                ratio = (ratio * 0xfff97272373d413259a46990580e213a) >> 128;
            }
            if (absTick & 0x4 != 0) {
                ratio = (ratio * 0xfff2e50f5f656932ef12357cf3c7fdcc) >> 128;
            }
            if (absTick & 0x8 != 0) {
                ratio = (ratio * 0xffe5caca7e10e4e61c3624eaa0941cd0) >> 128;
            }
            if (absTick & 0x10 != 0) {
                ratio = (ratio * 0xffcb9843d60f6159c9db58835c926644) >> 128;
            }
            if (absTick & 0x20 != 0) {
                ratio = (ratio * 0xff973b41fa98c081472e6896dfb254c0) >> 128;
            }
            if (absTick & 0x40 != 0) {
                ratio = (ratio * 0xff2ea16466c96a3843ec78b326b52861) >> 128;
            }
            if (absTick & 0x80 != 0) {
                ratio = (ratio * 0xfe5dee046a99a2a811c461f1969c3053) >> 128;
            }
            if (absTick & 0x100 != 0) {
                ratio = (ratio * 0xfcbe86c7900a88aedcffc83b479aa3a4) >> 128;
            }
            if (absTick & 0x200 != 0) {
                ratio = (ratio * 0xf987a7253ac413176f2b074cf7815e54) >> 128;
            }
            if (absTick & 0x400 != 0) {
                ratio = (ratio * 0xf3392b0822b70005940c7a398e4b70f3) >> 128;
            }
            if (absTick & 0x800 != 0) {
                ratio = (ratio * 0xe7159475a2c29b7443b29c7fa6e889d9) >> 128;
            }
            if (absTick & 0x1000 != 0) {
                ratio = (ratio * 0xd097f3bdfd2022b8845ad8f792aa5825) >> 128;
            }
            if (absTick & 0x2000 != 0) {
                ratio = (ratio * 0xa9f746462d870fdf8a65dc1f90e061e5) >> 128;
            }
            if (absTick & 0x4000 != 0) {
                ratio = (ratio * 0x70d869a156d2a1b890bb3df62baf32f7) >> 128;
            }
            if (absTick & 0x8000 != 0) {
                ratio = (ratio * 0x31be135f97d08fd981231505542fcfa6) >> 128;
            }
            if (absTick & 0x10000 != 0) {
                ratio = (ratio * 0x9aa508b5b7a84e1c677de54f3e99bc9) >> 128;
            }
            if (absTick & 0x20000 != 0) {
                ratio = (ratio * 0x5d6af8dedb81196699c329225ee604) >> 128;
            }
            if (absTick & 0x40000 != 0) {
                ratio = (ratio * 0x2216e584f5fa1ea926041bedfe98) >> 128;
            }
            if (absTick & 0x80000 != 0) {
                ratio = (ratio * 0x48a170391f7dc42444e8fa2) >> 128;
            }

            if (tick > 0) {
                ratio = type(uint256).max / ratio;
            }

            sqrtPriceX96 =
                uint160((ratio >> 32) + (ratio % (1 << 32) == 0 ? 0 : 1));
        }
    }

    function minTick() internal pure returns (int24) {
        return -887272;
    }

    function maxTick() internal pure returns (int24) {
        return 887272;
    }

    function minSqrtRatio() internal pure returns (uint160) {
        return 4295128739;
    }

    function maxSqrtRatio() internal pure returns (uint160) {
        return 1461446703485210103287273052203988822378723970342;
    }
}

contract UniswapV3MathHarness {
    function mostSignificantBit(uint256 x) external pure returns (uint8) {
        return UniswapV3BitMath.mostSignificantBit(x);
    }

    function leastSignificantBit(uint256 x) external pure returns (uint8) {
        return UniswapV3BitMath.leastSignificantBit(x);
    }

    function sqrtRatioAtTick(int24 tick) external pure returns (uint160) {
        return UniswapV3TickMath.getSqrtRatioAtTick(tick);
    }

    function minTick() external pure returns (int24) {
        return UniswapV3TickMath.minTick();
    }

    function maxTick() external pure returns (int24) {
        return UniswapV3TickMath.maxTick();
    }

    function minSqrtRatio() external pure returns (uint160) {
        return UniswapV3TickMath.minSqrtRatio();
    }

    function maxSqrtRatio() external pure returns (uint160) {
        return UniswapV3TickMath.maxSqrtRatio();
    }
}
