// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/FunctionMemberKinds.sol";

contract FunctionMemberKindsForgeTest {
    FunctionMemberKinds private target;

    function setUp() public {
        target = new FunctionMemberKinds();
    }

    function testNamespaceSelectors() public view {
        (bytes4 librarySelector, bytes4 interfaceSelector, bytes4 contractSelector) =
            target.namespaceSelectors();
        require(librarySelector == FunctionMemberLibrary.increment.selector);
        require(interfaceSelector == IFunctionMemberTarget.echo.selector);
        require(contractSelector == FunctionMemberTarget.echo.selector);
    }

    function testBoundFunctionMembers() public view {
        address receiver = address(0x1234);
        (
            bytes4 interfaceSelector,
            address interfaceAddress,
            bytes4 contractSelector,
            address contractAddress
        ) = target.boundMembers(receiver);
        require(interfaceSelector == IFunctionMemberTarget.echo.selector);
        require(interfaceAddress == receiver);
        require(contractSelector == FunctionMemberTarget.echo.selector);
        require(contractAddress == receiver);
    }

    function testEncodeCallNamespaces() public view {
        (bytes memory interfacePayload, bytes memory contractPayload) =
            target.encodeCalls();
        require(
            keccak256(interfacePayload) ==
                keccak256(abi.encodeWithSelector(IFunctionMemberTarget.echo.selector, 7))
        );
        require(
            keccak256(contractPayload) ==
                keccak256(abi.encodeWithSelector(FunctionMemberTarget.echo.selector, 9))
        );
    }
}
