// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract SkippedModifierReturn {
    uint256[] private stored;

    modifier maybe(bool run) {
        if (run) {
            _;
        }
    }

    function bad()
        internal
        maybe(false)
        returns (uint256[] storage result)
    {
        result = stored;
    }
}
