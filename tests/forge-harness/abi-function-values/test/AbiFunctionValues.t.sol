// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {
    AbiFunctionValueCallee,
    AbiFunctionValuesHarnessTarget
} from "../src/AbiFunctionValues.sol";

contract AbiFunctionValuesForgeTest {
    AbiFunctionValuesHarnessTarget private harness =
        new AbiFunctionValuesHarnessTarget();
    AbiFunctionValueCallee private callee = new AbiFunctionValueCallee();
    AbiFunctionValueCallee private other = new AbiFunctionValueCallee();

    function testMembersEqualityEncodeDecodeAndReturn() public {
        function(uint256) external returns (uint256) fn = callee.echo;

        (address addr, bytes4 selector) = harness.split(fn);
        require(addr == address(callee), "split address");
        require(selector == AbiFunctionValueCallee.echo.selector, "split selector");
        require(harness.same(fn, callee.echo), "same");
        require(!harness.same(fn, other.echo), "different");

        bytes memory encoded = harness.encode(fn);
        require(keccak256(encoded) == keccak256(abi.encode(fn)), "encode");

        function(uint256) external returns (uint256) returned =
            harness.returnEcho(address(callee));
        require(returned.address == address(callee), "return address");
        require(returned.selector == AbiFunctionValueCallee.echo.selector, "return selector");
    }

    function testCallThroughFunctionValue() public {
        uint256 result = harness.callEcho(callee.echo, 7);

        require(result == 8, "result");
        require(callee.last() == 7, "callee state");
    }

    function testPublicFunctionPointerGetterAndCall() public {
        harness.store(callee.echo);

        function(uint256) external returns (uint256) returned =
            harness.storedEcho();
        require(returned.address == address(callee), "getter address");
        require(returned.selector == AbiFunctionValueCallee.echo.selector, "getter selector");

        (address addr, bytes4 selector) = harness.storedMembers();
        require(addr == address(callee), "stored address");
        require(selector == AbiFunctionValueCallee.echo.selector, "stored selector");

        uint256 result = harness.callStored(11);
        require(result == 12, "stored call result");
        require(callee.last() == 11, "stored call state");
    }

    function testFunctionValueAbiRejectsDirtyPadding() public {
        bytes memory clean = abi.encode(callee.echo);
        clean[31] = 0x01;

        (bool ok, bytes memory data) = address(harness).call(
            abi.encodePacked(AbiFunctionValuesHarnessTarget.split.selector, clean)
        );

        require(!ok, "dirty accepted");
        require(data.length == 0, "dirty data");
    }
}
