// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PublicStorageParam {
    function bad(uint256[] storage values)
        public
        view
        returns (uint256)
    {
        return values.length;
    }
}
