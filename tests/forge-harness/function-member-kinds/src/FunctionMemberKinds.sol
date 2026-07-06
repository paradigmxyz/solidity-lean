// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library FunctionMemberLibrary {
    function increment(uint256 value) external pure returns (uint256) {
        return value + 1;
    }
}

interface IFunctionMemberTarget {
    function echo(uint256 value) external returns (uint256);
}

contract FunctionMemberTarget {
    function echo(uint256 value) external pure returns (uint256) {
        return value;
    }
}

contract FunctionMemberKinds {
    function namespaceSelectors()
        external
        pure
        returns (bytes4, bytes4, bytes4)
    {
        return (
            FunctionMemberLibrary.increment.selector,
            IFunctionMemberTarget.echo.selector,
            FunctionMemberTarget.echo.selector
        );
    }

    function boundMembers(address target)
        external
        pure
        returns (bytes4, address, bytes4, address)
    {
        return (
            IFunctionMemberTarget(target).echo.selector,
            IFunctionMemberTarget(target).echo.address,
            FunctionMemberTarget(target).echo.selector,
            FunctionMemberTarget(target).echo.address
        );
    }

    function encodeCalls()
        external
        pure
        returns (bytes memory, bytes memory)
    {
        return (
            abi.encodeCall(IFunctionMemberTarget.echo, (7)),
            abi.encodeCall(FunctionMemberTarget.echo, (9))
        );
    }
}
