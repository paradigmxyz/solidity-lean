// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract FnPtrReturnedDirectCallTarget {
    function plusOne(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    function get() internal pure
        returns (function(uint256) internal pure returns (uint256))
    {
        return plusOne;
    }

    function directReturn() external pure returns (uint256) {
        return get()(7);
    }

    function initializer() external pure returns (uint256) {
        uint256 value = get()(7);
        return value;
    }

    function encoded() external pure returns (bytes memory) {
        return abi.encode(get()(7));
    }

    function nested() external pure returns (uint256) {
        return get()(get()(7));
    }
}
