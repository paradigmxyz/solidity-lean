// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface IEncodeCallCallee {
    function foo(uint256 x) external;
}

// EC1 pin: `abi.encodeCall(fnPtr, args)` must derive the 4-byte selector AND the
// argument encode types from the callee's DECLARED parameter types, never from
// the argument expression types. These two functions bracket the bug: an
// argument narrower than the parameter, and an integer literal against a narrow
// parameter. Ground truth is pinned solc 0.8.35 + Forge/EVM (see the paired
// test).
contract EncodeCallSelectorHarnessTarget {
    // Repro B callee: a uint8-parameter external function of THIS contract.
    function foo(uint8 x) external {}

    // Repro A: argument `y` (uint8) is NARROWER than the declared parameter
    // (uint256). solc encodes the selector + argument from `foo(uint256)`
    // (0x2fbebd38), NOT `foo(uint8)` (0x11602fb3).
    function argNarrowerThanParam(IEncodeCallCallee i)
        external
        pure
        returns (bytes memory)
    {
        uint8 y = 3;
        return abi.encodeCall(i.foo, (y));
    }

    // Repro B: an integer LITERAL against a narrow (uint8) parameter. solc
    // encodes the selector + argument from `foo(uint8)` (0x11602fb3), NOT
    // `foo(uint256)` (0x2fbebd38, the literal's default uint256 type).
    function literalVsNarrowParam() external view returns (bytes memory) {
        return abi.encodeCall(this.foo, (3));
    }
}
