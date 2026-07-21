// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// BUG#6 (library-qualified signatures): solc renders public/external LIBRARY
// function signatures with the parameters' canonical SOURCE names — enums as
// `Lib.Mode`, structs as `Lib.S` (plus ` storage` for storage pointers), and
// contract types by NAME — not the external-ABI forms (`uint8`, `(uint256)`,
// `address`). Pinned against solc 0.8.35 `--hashes` + the real EVM:
//   isOff(Lib.Mode)      -> 0x02952002   (external-ABI form would be 0xac2ecd48)
//   idOf(C)              -> 0xbbf15d5e   (external-ABI form would be 0xd94fe832)
//   bump(Lib.S storage)  -> 0x83a5a0de   (external-ABI form would be 0x2a607935)

contract C {
    function id() external pure returns (uint256) {
        return 7;
    }
}

library Lib {
    enum Mode { Off, On }

    struct S {
        uint256 v;
    }

    function isOff(Mode m) public pure returns (bool) {
        return m == Mode.Off;
    }

    function idOf(C c) public pure returns (address) {
        return address(c);
    }

    function bump(S storage s) public {
        s.v += 1;
    }
}

contract LibraryQualifiedSelectorsHarnessTarget {
    Lib.S internal cell;

    function selIsOff() external pure returns (bytes4) {
        return Lib.isOff.selector;
    }

    function selIdOf() external pure returns (bytes4) {
        return Lib.idOf.selector;
    }

    function selBump() external pure returns (bytes4) {
        return Lib.bump.selector;
    }

    function callIsOff(uint8 m) external pure returns (bool) {
        return Lib.isOff(Lib.Mode(m));
    }

    function bumpTwice() external returns (uint256) {
        Lib.bump(cell);
        Lib.bump(cell);
        return cell.v;
    }
}
