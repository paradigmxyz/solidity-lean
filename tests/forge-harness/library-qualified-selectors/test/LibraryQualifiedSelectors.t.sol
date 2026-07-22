// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Lib, LibraryQualifiedSelectorsHarnessTarget} from "../src/LibraryQualifiedSelectors.sol";

contract LibraryQualifiedSelectorsForgeTest {
    LibraryQualifiedSelectorsHarnessTarget private target =
        new LibraryQualifiedSelectorsHarnessTarget();

    // The three audit-pinned library-qualified selectors, byte-exact.
    function testSelIsOffPinned() public view {
        require(target.selIsOff() == bytes4(0x02952002), "isOff(Lib.Mode)");
    }

    function testSelIdOfPinned() public view {
        require(target.selIdOf() == bytes4(0xbbf15d5e), "idOf(C)");
    }

    function testSelBumpPinned() public view {
        require(target.selBump() == bytes4(0x83a5a0de), "bump(Lib.S storage)");
    }

    // The selectors are NOT the external-ABI forms.
    function testSelectorsNotExternalAbiForms() public view {
        require(target.selIsOff() != bytes4(0xac2ecd48), "not isOff(uint8)");
        require(target.selIdOf() != bytes4(0xd94fe832), "not idOf(address)");
        require(target.selBump() != bytes4(0x2a607935), "not bump((uint256))");
    }

    // Real-EVM delegatecall dispatch round-trips through the qualified
    // selector (deployed-library linking): enum arg and storage-pointer arg.
    function testCallIsOffDispatch() public view {
        require(target.callIsOff(0), "isOff(Off)");
        require(!target.callIsOff(1), "!isOff(On)");
    }

    function testBumpStorageDispatch() public {
        require(target.bumpTwice() == 2, "bump twice");
    }
}
