// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// USINGFOR-WIDEN-BIND (#158) — `using L for uint8` attaching a library function
// whose FIRST parameter is WIDER than the target type. solc's function
// USABILITY rule (`Type::attachedFunctions`, Types.cpp) only requires the
// receiver to be IMPLICITLY CONVERTIBLE to the function's first-parameter type,
// so a `uint8` receiver binds `f(uint256 self)` (zero-extended, no truncation).
// The model formerly required exact-width shape and over-rejected. This harness
// pins the widened-receiver value (g(255) => 256) and the widened
// ADDITIONAL-ARG value on real solc/EVM. Self-contained; no user-typed state.
library L {
    function f(uint256 self) internal pure returns (uint256) {
        return self + 1;
    }

    function addWiden(uint256 self, uint256 a) internal pure returns (uint256) {
        return self + a;
    }
}

contract UsingForWidenHarnessTarget {
    using L for uint8;
    using L for uint256;

    // uint8 receiver widened to the uint256 first parameter of `f`.
    function widenReceiver(uint8 x) external pure returns (uint256) {
        return x.f();
    }

    // uint256 receiver (exact self) + uint8 additional arg widened to uint256.
    function widenAddArg(uint256 x, uint8 y) external pure returns (uint256) {
        return x.addWiden(y);
    }
}
