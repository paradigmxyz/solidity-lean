// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageToCalldataTuple {
    uint256[] private stored;
    uint256[] private other;

    function pair()
        internal
        view
        returns (uint256[] storage, uint256[] storage)
    {
        return (stored, other);
    }

    function bad() public view returns (uint256) {
        (uint256[] calldata leftAlias, uint256[] calldata rightAlias) = pair();
        return leftAlias.length + rightAlias.length;
    }
}
