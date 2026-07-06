// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExternalCalldataFunctionType {
    function target(uint256[] calldata values)
        external
        pure
        returns (uint256[] calldata)
    {
        return values;
    }

    function bad()
        external
        view
        returns (
            function(uint256[] calldata)
                external
                pure
                returns (uint256[] calldata)
        )
    {
        return this.target;
    }
}
