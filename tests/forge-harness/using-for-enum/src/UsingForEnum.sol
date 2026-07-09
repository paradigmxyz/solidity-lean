// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// EU1 pin: `using {f} for E` where E is an ENUM dispatches a member call
// `e.f(args)` to the bound free function / library function with the enum
// value passed by value as the first argument -- exactly as solc lowers
// `e.rank()` to `rank(e)`. Pins three binding forms over an enum receiver:
//   * file-level `using {rank} for Color global;`
//   * contract-level brace form `using {shift} for Color;`
//   * attached-library form `using ColorLib for Color;`

enum Color {
    Red,
    Green,
    Blue
}

// file-level global brace binding, single-arg member call
function rank(Color c) pure returns (uint256) {
    return uint256(c) + 1;
}

using {rank} for Color global;

// free function bound at contract level (brace form) with an extra argument
function shift(Color c, uint256 n) pure returns (uint256) {
    return uint256(c) + n;
}

// attached-library form
library ColorLib {
    function libRank(Color c) internal pure returns (uint256) {
        return uint256(c) * 10;
    }
}

contract UsingForEnumHarnessTarget {
    using {shift} for Color;
    using ColorLib for Color;

    // file-level global `using {rank} for Color global;` -> rank(c)
    function viaRank(uint256 x) public pure returns (uint256) {
        Color c = Color(x);
        return c.rank();
    }

    // contract-level `using {shift} for Color;` with an extra arg -> shift(c, n)
    function viaShift(uint256 x, uint256 n) public pure returns (uint256) {
        Color c = Color(x);
        return c.shift(n);
    }

    // attached-library `using ColorLib for Color;` -> ColorLib.libRank(c)
    function viaLib(uint256 x) public pure returns (uint256) {
        Color c = Color(x);
        return c.libRank();
    }
}
