// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataTuple {
    function pair(uint256[] memory left, uint256[] memory right)
        internal
        pure
        returns (uint256[] memory, uint256[] memory)
    {
        return (left, right);
    }

    function bad(uint256[] memory left, uint256[] memory right)
        public
        pure
        returns (uint256)
    {
        (uint256[] calldata leftAlias, uint256[] calldata rightAlias) =
            pair(left, right);
        return leftAlias.length + rightAlias.length;
    }
}
