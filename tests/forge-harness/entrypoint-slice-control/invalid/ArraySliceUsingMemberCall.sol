// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library ArraySliceUsingMemberLib {
    function first(uint256[] calldata input)
        internal
        pure
        returns (uint256)
    {
        return input[0];
    }
}

contract ArraySliceUsingMemberCall {
    using ArraySliceUsingMemberLib for uint256[];

    function bad(uint256[] calldata input) external pure returns (uint256) {
        return input[1:3].first();
    }
}
