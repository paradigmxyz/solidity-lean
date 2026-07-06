// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface IAbiFunctionValueCallee {
    function echo(uint256 value) external returns (uint256);
}

contract AbiFunctionValueCallee {
    uint256 public last;

    function echo(uint256 value) external returns (uint256) {
        last = value;
        return value + 1;
    }
}

contract AbiFunctionValuesHarnessTarget {
    function(uint256) external returns (uint256) public storedEcho;

    function store(function(uint256) external returns (uint256) fn) external {
        storedEcho = fn;
    }

    function storedMembers() external view returns (address, bytes4) {
        return (storedEcho.address, storedEcho.selector);
    }

    function split(function(uint256) external returns (uint256) fn)
        external
        pure
        returns (address, bytes4)
    {
        return (fn.address, fn.selector);
    }

    function same(
        function(uint256) external returns (uint256) left,
        function(uint256) external returns (uint256) right
    ) external pure returns (bool) {
        return left == right;
    }

    function encode(function(uint256) external returns (uint256) fn)
        external
        pure
        returns (bytes memory)
    {
        return abi.encode(fn);
    }

    function returnEcho(address target)
        external
        pure
        returns (function(uint256) external returns (uint256))
    {
        return IAbiFunctionValueCallee(target).echo;
    }

    function callEcho(
        function(uint256) external returns (uint256) fn,
        uint256 value
    ) external returns (uint256) {
        return fn(value);
    }

    function callStored(uint256 value) external returns (uint256) {
        return storedEcho(value);
    }
}
