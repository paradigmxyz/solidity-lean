// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import "../src/DispatchOom.sol";

contract DispatchOomForgeTest {
    DispatchOom private target;

    function setUp() public {
        target = new DispatchOom();
    }

    // offset(0x20) ++ length(2^64): an oversized dynamic length.
    function oversizedArgs() internal pure returns (bytes memory) {
        return bytes.concat(bytes32(uint256(0x20)), bytes32(uint256(2 ** 64)));
    }

    function panic0x41() internal pure returns (bytes memory) {
        return abi.encodeWithSignature("Panic(uint256)", uint256(0x41));
    }

    // EAGER `bytes memory` param with an oversized length -> Panic(0x41).
    function testMemoryBytesOversizedLengthPanics() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(DispatchOom.memBytesLength.selector, oversizedArgs())
        );
        require(!success, "mem bytes should revert");
        require(
            keccak256(output) == keccak256(panic0x41()),
            "mem bytes should Panic(0x41)"
        );
    }

    // CONTROL: LAZY `bytes calldata` param, SAME oversized length -> empty.
    function testCalldataBytesOversizedLengthEmptyRevert() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DispatchOom.calldataBytesLength.selector,
                oversizedArgs()
            )
        );
        require(!success, "calldata bytes should revert");
        require(output.length == 0, "calldata bytes should be empty revert");
    }

    // EAGER `uint256[] memory` param with an oversized length -> Panic(0x41).
    function testMemoryUintArrayOversizedLengthPanics() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DispatchOom.memUintArrayLength.selector,
                oversizedArgs()
            )
        );
        require(!success, "mem uint[] should revert");
        require(
            keccak256(output) == keccak256(panic0x41()),
            "mem uint[] should Panic(0x41)"
        );
    }

    // CONTROL: LAZY `uint256[] calldata` param, SAME length -> empty.
    function testCalldataUintArrayOversizedLengthEmptyRevert() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DispatchOom.calldataUintArrayLength.selector,
                oversizedArgs()
            )
        );
        require(!success, "calldata uint[] should revert");
        require(output.length == 0, "calldata uint[] should be empty revert");
    }

    // CONTROL: a well-formed EAGER `bytes memory` decode is unchanged.
    function testMemoryBytesValidDecode() public {
        (bool success, bytes memory output) = address(target).call(
            bytes.concat(
                DispatchOom.memBytesLength.selector,
                abi.encode(bytes("abc"))
            )
        );
        require(success, "valid mem bytes should succeed");
        require(abi.decode(output, (uint256)) == 3, "length should be 3");
    }

    // TC-OOM1: a SUCCESSFUL try-call whose returndata carries an oversized
    // dynamic length -> Panic(0x41) propagates UNCAUGHT (not routed to catch).
    function testTryCatchSuccessOversizedReturnPanics() public {
        DispatchOomReturnHuge returner = new DispatchOomReturnHuge();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(DispatchOom.tryBytesLength, (address(returner)))
        );
        require(!success, "try huge return should revert");
        require(
            keccak256(output) == keccak256(panic0x41()),
            "try huge return should Panic(0x41)"
        );
    }

    // CONTROL: a genuinely-short success returndata -> empty decode revert
    // (uncaught), NOT the 0xdead catch sentinel and NOT a panic.
    function testTryCatchSuccessShortReturnEmptyRevert() public {
        DispatchOomReturnShort returner = new DispatchOomReturnShort();
        (bool success, bytes memory output) = address(target).call(
            abi.encodeCall(DispatchOom.tryBytesLength, (address(returner)))
        );
        require(!success, "try short return should revert");
        require(output.length == 0, "try short return should be empty revert");
    }
}
