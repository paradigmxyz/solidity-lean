// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PublicInternalFunctionPointerParam {
    function bad(function() internal pure returns (uint256) getter)
        public
        pure
        returns (uint256)
    {
        getter;
        return 1;
    }
}
