// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LibraryEnumOverloadsHarnessTarget} from "../src/LibraryEnumOverloads.sol";

contract LibraryEnumOverloadsForgeTest {
    LibraryEnumOverloadsHarnessTarget private target =
        new LibraryEnumOverloadsHarnessTarget();

    // solc ACCEPTS the enum-distinct library overloads (this suite compiling
    // at all is the acceptance control) and the real-EVM delegatecall
    // dispatches each call to the RIGHT overload — the qualified signatures
    // `f(OvLib.EnumA)` / `f(OvLib.EnumB)` hash to distinct selectors.
    function testOverloadA() public view {
        require(target.callA(1) == 101, "f(EnumA)");
    }

    function testOverloadB() public view {
        require(target.callB(2) == 202, "f(EnumB)");
    }
}
