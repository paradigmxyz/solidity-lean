// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract TerminalStatementsHarnessTarget {
    error Pair(uint256 first, uint256 second);

    uint256 public x;

    function explicitReturn(uint256 value)
        external
        pure
        returns (uint256 first, uint256 second)
    {
        return (value, value + 1);
    }

    function namedFallthrough(uint256 value)
        external
        pure
        returns (uint256 out)
    {
        out = value + 2;
    }

    function revertString() external pure {
        revert("terminal");
    }

    function revertCustom(uint256 value) external pure {
        revert Pair({second: value + 1, first: value});
    }

    function destroy(address payable recipient) external {
        selfdestruct(recipient);
        x = 99;
    }
}
