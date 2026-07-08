// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/AbiMemoryEager.sol";

contract AbiMemoryEagerForgeTest {
    AbiMemoryEager private target;

    function setUp() public {
        target = new AbiMemoryEager();
    }

    // uint8[] with length 1 whose single element is 256 (dirty for uint8).
    function dirtyArrayArgs() internal pure returns (bytes memory) {
        return abi.encodePacked(uint256(0x20), uint256(1), uint256(256));
    }

    // NarrowPair (uint8,uint8) with a clean first (7) and dirty second (256).
    function dirtyPairArgs() internal pure returns (bytes memory) {
        return abi.encodePacked(uint256(7), uint256(256));
    }

    function testMemoryArrayEagerRevert() public {
        (bool ok, bytes memory out) = address(target).call(
            abi.encodePacked(AbiMemoryEager.memArrayLength.selector, dirtyArrayArgs())
        );
        // Memory aggregate: eager element validation reverts even though the
        // function only reads `.length`. solc's decode validator reverts empty.
        require(!ok, "memory array must revert");
        require(out.length == 0, "memory array empty revert");
    }

    function testCalldataArrayLazySuccess() public {
        (bool ok, bytes memory out) = address(target).call(
            abi.encodePacked(AbiMemoryEager.cdArrayLength.selector, dirtyArrayArgs())
        );
        // Calldata aggregate: element validated lazily on access; `.length`
        // never touches the dirty element, so the call succeeds returning 1.
        require(ok, "calldata array must succeed");
        require(abi.decode(out, (uint256)) == 1, "calldata array length");
    }

    function testMemoryPairEagerRevert() public {
        (bool ok, bytes memory out) = address(target).call(
            abi.encodePacked(AbiMemoryEager.memPairFirst.selector, dirtyPairArgs())
        );
        // Memory struct: the dirty `second` element is validated eagerly even
        // though only `first` is read.
        require(!ok, "memory pair must revert");
        require(out.length == 0, "memory pair empty revert");
    }

    function testCalldataPairLazySuccess() public {
        (bool ok, bytes memory out) = address(target).call(
            abi.encodePacked(AbiMemoryEager.cdPairFirst.selector, dirtyPairArgs())
        );
        // Calldata struct: only `first` (7) is read; the dirty `second` is not
        // validated, so the call succeeds.
        require(ok, "calldata pair must succeed");
        require(abi.decode(out, (uint8)) == 7, "calldata pair first");
    }
}
