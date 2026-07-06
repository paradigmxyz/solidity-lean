// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PublicStorageReturn {
    uint256[] values;

    function bad()
        public
        view
        returns (uint256[] storage result)
    {
        return values;
    }
}
