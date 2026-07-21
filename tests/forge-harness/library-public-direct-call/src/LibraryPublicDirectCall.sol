// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

library ModeLib {
    enum Mode { Off, On }

    function isOff(Mode m) public pure returns (bool) {
        return m == Mode.Off;
    }
}

contract LibraryPublicDirectCallHarnessTarget {
    function check(uint8 m) external pure returns (bool) {
        return ModeLib.isOff(ModeLib.Mode(m));
    }
}
